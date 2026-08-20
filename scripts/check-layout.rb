#!/usr/bin/env ruby
# frozen_string_literal: true

require "json"
require "find"
require "pathname"
require "psych"
require "yaml"

ROOT = Pathname.new(__dir__).parent.realpath
EXPECTED = %w[
  21890733
  21892986
  21892995
  21892997
  21925458
  21925574
  21925578
  21925582
  21986230
].freeze
STANDARD_AXIOMS = ["propext", "Quot.sound", "Classical.choice"].freeze
CONFIG_KEYS = %w[
  challenge_module
  solution_module
  theorem_names
  definition_names
  permitted_axioms
  enable_nanoda
].freeze
SOURCE_RELATIONSHIPS = %w[
  formalizes adapts independently-proves background other
].freeze

errors = []
warnings = []

def scalar_key(node)
  node.is_a?(Psych::Nodes::Scalar) ? node.value : nil
end

def check_yaml_nodes(node, file, errors)
  case node
  when Psych::Nodes::Mapping
    seen = {}
    node.children.each_slice(2) do |key, value|
      name = scalar_key(key)
      if name
        errors << "#{file}: YAML merge keys are not allowed" if name == "<<"
        errors << "#{file}: duplicate YAML key #{name.inspect}" if seen[name]
        seen[name] = true
      end
      check_yaml_nodes(value, file, errors)
    end
  when Psych::Nodes::Sequence, Psych::Nodes::Document, Psych::Nodes::Stream
    node.children.each { |child| check_yaml_nodes(child, file, errors) }
  when Psych::Nodes::Alias
    errors << "#{file}: YAML aliases are not allowed"
  end
end

def nonempty_string?(value)
  value.is_a?(String) && !value.strip.empty?
end

def read_utf8(path)
  File.read(path.to_s, encoding: "UTF-8")
end

projects = ROOT.glob("zenodo-*/palomar").select(&:directory?).sort
actual = projects.map { |path| path.parent.basename.to_s.delete_prefix("zenodo-") }
errors << "expected DOI directories #{EXPECTED.inspect}, found #{actual.inspect}" unless actual == EXPECTED

licence_pattern = /\A(?:license|licence|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?\z/i
root_licences = ROOT.children.select { |path| path.file? && path.basename.to_s.match?(licence_pattern) }
errors << "repository root must contain exactly one conventional licence file" unless root_licences.map { |p| p.basename.to_s } == ["LICENSE"]

projects.each do |project|
  label = project.relative_path_from(ROOT).to_s
  paper = project.parent
  %w[README.md preprint.pdf].each do |name|
    errors << "#{label}: missing ../#{name}" unless paper.join(name).file?
  end
  %w[Challenge.lean Solution.lean comparator.json formalization.yaml lean-toolchain lake-manifest.json].each do |name|
    errors << "#{label}: missing #{name}" unless project.join(name).file?
  end

  lakefiles = %w[lakefile.toml lakefile.lean].select { |name| project.join(name).file? }
  errors << "#{label}: expected exactly one Lake file" unless lakefiles.length == 1
  next unless %w[Challenge.lean Solution.lean comparator.json formalization.yaml lean-toolchain lake-manifest.json].all? { |name| project.join(name).file? }

  toolchain = read_utf8(project.join("lean-toolchain")).strip
  match = toolchain.match(/\Aleanprover\/lean4:v(\d+)\.(\d+)\.(\d+)\z/)
  if match.nil?
    errors << "#{label}: malformed lean-toolchain #{toolchain.inspect}"
  elsif ([match[1].to_i, match[2].to_i] <=> [4, 28]) == -1
    errors << "#{label}: Lean #{match[1]}.#{match[2]} is below Palomar's checked v4.28 floor"
  end

  begin
    config = JSON.parse(read_utf8(project.join("comparator.json")))
    unknown = config.keys - CONFIG_KEYS
    errors << "#{label}: unknown Comparator keys #{unknown.inspect}" unless unknown.empty?
    %w[challenge_module solution_module theorem_names permitted_axioms].each do |key|
      errors << "#{label}: Comparator is missing #{key}" unless config.key?(key)
    end
    errors << "#{label}: Challenge and Solution modules must differ" if config["challenge_module"] == config["solution_module"]
    unless config["theorem_names"].is_a?(Array) && !config["theorem_names"].empty? && config["theorem_names"].all? { |name| nonempty_string?(name) }
      errors << "#{label}: theorem_names must be a nonempty string list"
    end
    unless config["permitted_axioms"].is_a?(Array) && (config["permitted_axioms"] - STANDARD_AXIOMS).empty?
      errors << "#{label}: permitted_axioms contains a nonstandard axiom"
    end
    if config.key?("definition_names") && !config["definition_names"].is_a?(Array)
      errors << "#{label}: definition_names must be a list"
    end
    if config.key?("enable_nanoda") && config["enable_nanoda"] != true
      errors << "#{label}: enable_nanoda, when present, must be true"
    end
  rescue JSON::ParserError => e
    errors << "#{label}: invalid comparator.json: #{e.message}"
  end

  metadata_file = project.join("formalization.yaml")
  begin
    syntax = Psych.parse_file(metadata_file.to_s)
    check_yaml_nodes(syntax, metadata_file.relative_path_from(ROOT), errors)
    metadata = YAML.safe_load(read_utf8(metadata_file), permitted_classes: [], aliases: false)
    unless metadata.is_a?(Hash)
      errors << "#{label}: formalization.yaml must contain one mapping"
      next
    end
    errors << "#{label}: metadata version must be v0.4" unless metadata["version"] == "v0.4"
    project_data = metadata["project"]
    unless project_data.is_a?(Hash)
      errors << "#{label}: metadata project mapping is missing"
      next
    end
    errors << "#{label}: project.name is missing" unless nonempty_string?(project_data["name"])
    description = project_data["description"]
    errors << "#{label}: project.description is missing or over 10,000 characters" unless nonempty_string?(description) && description.length <= 10_000
    %w[authors responsible_maintainers].each do |key|
      value = project_data[key]
      errors << "#{label}: project.#{key} must be a nonempty name list" unless value.is_a?(Array) && !value.empty? && value.all? { |name| nonempty_string?(name) }
    end
    errors << "#{label}: project.license must match root MIT licence" unless project_data["license"] == "MIT"

    classification = metadata["classification"] || {}
    arxiv = classification["arxiv"]
    msc = classification["msc2020"]
    errors << "#{label}: classification.arxiv must contain 1–2 distinct codes" unless arxiv.is_a?(Array) && (1..2).cover?(arxiv.length) && arxiv.uniq == arxiv && arxiv.all? { |code| nonempty_string?(code) }
    errors << "#{label}: classification.msc2020 must contain 1–8 distinct five-character codes" unless msc.is_a?(Array) && (1..8).cover?(msc.length) && msc.uniq == msc && msc.all? { |code| code.is_a?(String) && code.match?(/\A\d{2}[A-Z]\d{2}\z/) }

    sources = metadata["sources"]
    unless sources.is_a?(Array) && !sources.empty? && sources.all? { |source| source.is_a?(Hash) && nonempty_string?(source["title"]) && SOURCE_RELATIONSHIPS.include?(source["relationship"]) }
      errors << "#{label}: sources must be nonempty and use Palomar relationships"
    end
    methods = metadata.dig("automation", "methods")
    unless methods.is_a?(Array) && !methods.empty? && methods.all? { |method| method.is_a?(Hash) && nonempty_string?(method["method"]) }
      errors << "#{label}: automation.methods must be nonempty"
    end
    errors << "#{label}: review.status is missing" unless nonempty_string?(metadata.dig("review", "status"))
    reported_axioms = metadata.dig("status", "axioms")
    unless reported_axioms.is_a?(Array) && (reported_axioms - STANDARD_AXIOMS).empty?
      errors << "#{label}: status.axioms must be a list containing only standard axioms"
    end
  rescue Psych::Exception => e
    errors << "#{label}: invalid formalization.yaml: #{e.message}"
  end

  begin
    manifest = JSON.parse(read_utf8(project.join("lake-manifest.json")))
    Array(manifest["packages"]).each do |package|
      next unless package["type"] == "git"
      rev = package["rev"]
      url = package["url"]
      errors << "#{label}: package #{package['name']} lacks a full lowercase SHA" unless rev.is_a?(String) && rev.match?(/\A[0-9a-f]{40}\z/)
      errors << "#{label}: package #{package['name']} is not a public GitHub URL" unless url.is_a?(String) && url.match?(%r{\Ahttps://github\.com/[^/]+/[^/]+/?\z})
    end
  rescue JSON::ParserError => e
    errors << "#{label}: invalid lake-manifest.json: #{e.message}"
  end

  challenge = project.join("Challenge.lean")
  challenge_lines = File.foreach(challenge.to_s, encoding: "UTF-8").count
  errors << "#{label}: Challenge exceeds 1,000 lines" if challenge_lines > 1_000
  errors << "#{label}: Challenge exceeds 100 KiB" if challenge.size > 100 * 1024
  warnings << "#{label}: Challenge exceeds the 300-line warning threshold" if challenge_lines > 300
  warnings << "#{label}: Challenge exceeds the 32-KiB warning threshold" if challenge.size > 32 * 1024

  solution_text = read_utf8(project.join("Solution.lean"))
  errors << "#{label}: Solution contains sorry" if solution_text.match?(/\bsorry\b/)
  %w[Challenge.lean Solution.lean].each do |name|
    text = read_utf8(project.join(name))
    errors << "#{label}: #{name} mentions a banned native proof primitive" if text.match?(/\bnative_decide\b|Lean\.ofReduceBool/)
  end
end

ROOT.find do |path|
  next if path == ROOT
  if path.directory? && path.basename.to_s == ".lake"
    Find.prune
    next
  end
  if path.symlink?
    errors << "#{path.relative_path_from(ROOT)}: symlinks are not allowed in the submission snapshot"
    Find.prune if path.directory?
  end
  next unless path.file?
  relative = path.relative_path_from(ROOT).to_s
  next if relative.split("/").include?(".lake")
  errors << "#{relative}: compiled Lean artifact outside .lake" if relative.match?(/\.(?:olean|ilean|a|bc|dll|dylib|o|obj|so|trace)\z/)
  errors << "#{relative}: Git LFS pointer detected" if path.size < 1024 && File.binread(path.to_s).start_with?("version https://git-lfs.github.com/spec/v1")
end

warnings.each { |warning| warn "warning: #{warning}" }
if errors.empty?
  puts "OK: #{projects.length} Palomar projects passed the local structural preflight."
else
  errors.each { |error| warn "error: #{error}" }
  abort "FAILED: #{errors.length} local preflight error(s)."
end
