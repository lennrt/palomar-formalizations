#!/usr/bin/env python3
"""Reproduce local Palomar checks without submitting or publishing anything.

Requires Python 3.11+, PyYAML, the pinned Lean toolchain, a clean checkout of
PalomarSubmission at TOOLS_REVISION, and materialized project dependencies.
Rendering additionally needs the pinned Verso checkout and its dependencies.
Local macOS execution does not exercise Palomar's hosted Linux confinement.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import shutil
import subprocess
import sys
import time

TOOLS_REVISION = 'd4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44'
VERSO_REVISION = '9f8096e40b31715b1d8d5997f15a0bd832f7e37d'
REPOSITORY = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def sources(root):
    for directory, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in {'.lake', '.git', '__pycache__'})
        for name in sorted(files):
            p = Path(directory) / name
            if p.suffix == '.lean':
                yield p


def fingerprints(project):
    paths = list(sources(project)) + [project / n for n in (
        'comparator.json', 'formalization.yaml', 'lake-manifest.json',
        'lakefile.toml', 'lean-toolchain')]
    return {str(p.relative_to(project)): sha(p) for p in sorted(paths)}


def output(command, cwd):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def run(command, cwd, log):
    start = time.monotonic()
    print('Running ' + ' '.join(str(x) for x in command[:5]), flush=True)
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open('w') as stream:
        proc = subprocess.run([str(x) for x in command], cwd=cwd,
                              stdout=stream, stderr=subprocess.STDOUT)
    record = {'command': [str(x) for x in command], 'exit_code': proc.returncode,
              'seconds': round(time.monotonic() - start, 3)}
    if proc.returncode:
        print(log.read_text()[-12000:], flush=True)
        raise RuntimeError(f'Command failed; see {log}')
    return record


def clean_revision(path, expected):
    revision = output(['git', 'rev-parse', 'HEAD'], path)
    if revision != expected:
        raise RuntimeError(f'{path}: expected revision {expected}, found {revision}')
    if output(['git', 'status', '--porcelain', '--untracked-files=all'], path):
        raise RuntimeError(f'{path}: modified or untracked files are present')


def preflight(project, tools, evidence):
    from scripts.source_requirements import inspect_lean_sources
    from scripts.submission_contract import load_formalization_metadata
    from scripts.verify_submission import load_comparator_config, manifest_packages, parse_lean_header
    for name in ('Challenge.lean', 'Solution.lean', 'comparator.json', 'formalization.yaml',
                 'lakefile.toml', 'lean-toolchain', 'lake-manifest.json'):
        path = project / name
        if path.is_symlink() or not path.is_file():
            raise RuntimeError(f'Expected regular file: {path}')
    if (project / 'lakefile.lean').exists():
        raise RuntimeError('This verifier expects exactly one lakefile.toml')
    metadata = load_formalization_metadata(project / 'formalization.yaml')
    config = load_comparator_config(project / 'comparator.json')
    report, issues = inspect_lean_sources(REPOSITORY)
    if issues:
        raise RuntimeError('\n'.join(str(x) for x in issues))
    minimum = json.loads((tools / 'toolchains.json').read_text())['minimum']
    toolchain = (project / 'lean-toolchain').read_text().strip()
    if toolchain != 'leanprover/lean4:' + minimum:
        raise RuntimeError('Recheck current accepted toolchain before using this verifier')
    packages = manifest_packages(project)
    for package in packages:
        path = (project / '.lake/packages' / package['name']).resolve(strict=True)
        clean_revision(path, package['revision'])
        origin = output(['git', 'remote', 'get-url', 'origin'], path).removesuffix('.git').lower()
        if origin != package['url'].removesuffix('.git').lower():
            raise RuntimeError(f'Dependency remote mismatch: {package["name"]}')
        if package['name'] == 'mathlib' and (path / 'lean-toolchain').read_text().strip() != toolchain:
            raise RuntimeError('Pinned Mathlib uses a different Lean toolchain')
    headers = []
    for path in sources(project):
        raw = output(['lake', 'env', 'lean', '--deps-json', str(path)], project)
        header = parse_lean_header(raw)
        if not header.is_module:
            raise RuntimeError(f'Missing compiler module header: {path}')
        headers.append({'path': str(path.relative_to(project)),
                        'imports': header.imports, 'module': True})
        if path.name == 'Challenge.lean':
            if path.stat().st_size > 100 * 1024 or len(path.read_text().splitlines()) > 1000:
                raise RuntimeError('Challenge exceeds the official size limits')
            if any(m != 'Mathlib' and not m.startswith('Mathlib.') for m in header.imports):
                raise RuntimeError('This local verifier expects a Mathlib-only Challenge')
    write(evidence / 'module-headers.json', headers)
    return {'metadata': 'passed', 'repository_source_policy': report,
            'compiler_module_headers': len(headers),
            'project_name': metadata['project']['name'], 'toolchain': toolchain,
            'comparator_configuration': 'passed', 'selected_theorems': len(config['theorem_names']),
            'verified_dependency_sources': packages}


def compare(project, evidence, local):
    from scripts.verify_submission import load_comparator_config
    if local and platform.system() != 'Darwin':
        raise RuntimeError('The explicit local exception is restricted to macOS')
    prefix = Path(output(['lake', 'env', 'lean', '--print-prefix'], project))
    binaries = {n: prefix / 'bin' / n for n in
                ('lean', 'lake', 'leanexport', 'leanchecker', 'nanoda_bin', 'con-ron')}
    if any(not p.is_file() for p in binaries.values()):
        raise RuntimeError('Missing bundled proof checkers')
    config = load_comparator_config(project / 'comparator.json')
    config.pop('enable_nanoda', None)
    config['external_kernels'] = {n: [str(binaries[b])] for n, b in
                                  [('nanoda', 'nanoda_bin'), ('con-ron', 'con-ron')]}
    target = project / '.lake' / 'local-verification' / 'comparator.json'
    write(target, config)
    command = ['lake', 'comparator', '--config', str(target)]
    if local:
        command.append('--inadvisably-no-sandbox')
    record = run(command, project, evidence / 'comparison.log')
    record.update({'status': 'passed', 'tool_sha256': {n: sha(p) for n, p in binaries.items()},
                   'selected_theorems': len(config['theorem_names']),
                   'configuration': config,
                   'comparison_sandbox': 'disabled_local_macos' if local else 'bubblewrap'})
    return record


def render(project, tools, evidence, verso, renderer_packages):
    from scripts.render_challenge import merge_renderer_manifest, trusted_lakefile
    from scripts.verify_submission import load_comparator_config
    clean_revision(verso, VERSO_REVISION)
    config = load_comparator_config(project / 'comparator.json')
    command = ['lake', 'env', 'lean', '--run',
               str(tools / 'scripts/core_notation_audit.lean'), config['challenge_module']]
    for key, kind in [('theorem_names', 'theorem'), ('definition_names', 'def')]:
        for name in config.get(key, []):
            command += [kind, name]
    core_log = evidence / 'core-notation.log'
    core = run(command, project, core_log)
    declarations = json.loads(core_log.read_text().splitlines()[-1])
    audit = evidence / 'audit-declarations.json'
    write(audit, declarations)
    workspace = project / '.lake/local-render/workspace'
    workspace.mkdir(parents=True, exist_ok=True)
    for name in ('Challenge.lean', 'Solution.lean', 'comparator.json', 'lean-toolchain'):
        shutil.copy2(project / name, workspace / name)
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    merged = merge_renderer_manifest(manifest, json.loads((verso / 'lake-manifest.json').read_text()),
                                     VERSO_REVISION)
    write(workspace / 'lake-manifest.json', merged)
    (workspace / 'lakefile.toml').write_text(trusted_lakefile(
        manifest, VERSO_REVISION, challenge_module=config['challenge_module'],
        challenge_source_root=PurePosixPath('.')))
    packages = workspace / '.lake/packages'
    packages.mkdir(parents=True, exist_ok=True)
    for package in merged['packages']:
        name = package['name']
        if name == 'verso':
            src = verso
        elif (project / '.lake/packages' / name).exists():
            src = (project / '.lake/packages' / name).resolve()
        else:
            src = (renderer_packages / name).resolve(strict=True)
        clean_revision(src, package['rev'])
        dst = packages / name
        if dst.is_symlink() and dst.resolve() != src:
            dst.unlink()
        if not dst.exists():
            dst.symlink_to(src, target_is_directory=True)
    literate = run(['lake', 'build', 'Challenge:literate'], workspace, evidence / 'literate.log')
    raw = workspace / '.lake/build/palomar-render-raw'
    if raw.exists():
        shutil.rmtree(raw)
    html = run(['lake', 'exe', 'verso-html', workspace / '.lake/build/literate', raw],
               workspace, evidence / 'html.log')
    clean = workspace / '.lake/build/palomar-render-clean'
    if clean.exists():
        shutil.rmtree(clean)
    clean.mkdir(parents=True)
    prefix = Path(output(['lake', 'env', 'lean', '--print-prefix'], project))
    command = ['lake', 'env', sys.executable, '-B', tools / 'scripts/render_challenge.py',
               'sanitize', '--input-dir', raw, '--output-dir', clean,
               '--challenge', workspace / 'Challenge.lean', '--solution', workspace / 'Solution.lean',
               '--comparator', workspace / 'comparator.json', '--challenge-module',
               config['challenge_module'], '--lean', prefix / 'bin/lean',
               '--diagnostic-out', evidence / 'sanitize-diagnostic.json',
               '--audit-declarations', audit]
    sanitize = run(command, workspace, evidence / 'sanitize.log')
    entry = clean / 'Challenge/index.html'
    if not entry.is_file():
        raise RuntimeError('Rendered Challenge entrypoint is missing')
    return {'status': 'passed', 'core_notation': core, 'literate': literate, 'html': html,
            'sanitize': sanitize, 'rendered_declarations': len(declarations),
            'renderer_revision': VERSO_REVISION,
            'renderer_dependencies': [{'name': p['name'], 'revision': p['rev']} for p in merged['packages']],
            'entrypoint': str(entry.relative_to(project)), 'entrypoint_sha256': sha(entry)}


def seal_release(project, evidence, preflight_result):
    """Bind final inputs to completed checks, allowing only a revalidated metadata edit."""
    from scripts.render_challenge import artifact_manifest
    all_path = evidence / 'all.json'
    previous = json.loads(all_path.read_text())
    current = fingerprints(project)
    old = previous['input_sha256']
    changes = {name: {'checked': old.get(name), 'current': current.get(name)}
               for name in old.keys() | current.keys() if old.get(name) != current.get(name)}
    if set(changes) - {'formalization.yaml'}:
        raise RuntimeError('Proof/build/render inputs changed; rerun all checks before release')
    if previous['status'] != 'passed' or not previous['inputs_unchanged']:
        raise RuntimeError('The complete check suite has not passed for a stable snapshot')
    if previous['official_tools_commit'] != TOOLS_REVISION:
        raise RuntimeError('Release and full verification use different official tools')
    stages = [previous['build'], previous['kernel_replay'], previous['comparison']]
    stages += [previous['render'][name] for name in ('core_notation', 'literate', 'html', 'sanitize')]
    if any(stage['exit_code'] != 0 for stage in stages):
        raise RuntimeError('A required verification stage failed')
    entry = project / previous['render']['entrypoint']
    if sha(entry) != previous['render']['entrypoint_sha256']:
        raise RuntimeError('Sanitized rendering changed after verification')
    bundle = entry.parent.parent
    files, tree = artifact_manifest(bundle)
    manifest = json.loads((bundle / 'artifact-manifest.json').read_text())
    if manifest['artifact_tree_sha256'] != tree or manifest['files'] != files:
        raise RuntimeError('Sanitized rendering artifact manifest does not match the bundle')
    experiments = json.loads((evidence / 'experiments.json').read_text())
    for group in ('program_sha256', 'logs'):
        for name, digest in experiments[group].items():
            if sha(project / name) != digest:
                raise RuntimeError('Finite experiment evidence changed: ' + name)
    return {'status': 'passed', 'input_sha256': current, 'preflight': preflight_result,
            'full_verification_report': 'all.json', 'full_verification_report_sha256': sha(all_path),
            'metadata_only_refresh': changes,
            'proof_build_and_render_inputs_unchanged': True,
            'artifact_tree_sha256': tree, 'rendered_files': len(files),
            'selected_theorems': previous['comparison']['selected_theorems'],
            'experiments_report_sha256': sha(evidence / 'experiments.json')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('project', type=Path, help='Path to the selected palomar directory')
    parser.add_argument('--submission-tools', type=Path, required=True)
    parser.add_argument('--stage', choices=['preflight', 'replay', 'comparison', 'render', 'all', 'release'], default='all')
    parser.add_argument('--allow-unsandboxed-local-comparison', action='store_true')
    parser.add_argument('--verso', type=Path)
    parser.add_argument('--renderer-packages', type=Path)
    args = parser.parse_args()
    project, tools = args.project.resolve(), args.submission_tools.resolve()
    project.relative_to(REPOSITORY)
    clean_revision(tools, TOOLS_REVISION)
    sys.path.insert(0, str(tools))
    evidence = project / 'verification'
    evidence.mkdir(exist_ok=True)
    before = fingerprints(project)
    report = {'status': 'running', 'stage': args.stage, 'host': platform.system(),
              'service_verification': False, 'editorial_review': False, 'registered': False,
              'not_exercised': ['hosted Linux confinement and resource controls',
                  'hosted canonical Challenge compilation and transitive dependency audit',
                  'hosted positive/negative verifier controls', 'fresh download of dependency build caches',
                  'hosted licence/ORCID/network provenance checks', 'Palomar editorial judgments'],
              'official_tools_commit': TOOLS_REVISION, 'input_sha256': before,
              'verifier_sha256': sha(Path(__file__)),
              'official_source_sha256': {str(p.relative_to(tools)): sha(p) for p in [
                  tools / 'scripts/render_challenge.py', tools / 'scripts/core_notation_audit.lean',
                  tools / 'scripts/source_requirements.py', tools / 'scripts/submission_contract.py']}}
    result = evidence / (args.stage + '.json')
    write(result, report)
    try:
        report['preflight'] = preflight(project, tools, evidence)
        if args.stage == 'release':
            report['release'] = seal_release(project, evidence, report['preflight'])
        if args.stage == 'all':
            report['build'] = run(['lake', 'build'], project, evidence / 'build.log')
        if args.stage in ('all', 'replay'):
            report['kernel_replay'] = run(['lake', 'env', 'leanchecker', '--fresh', 'Solution'],
                                          project, evidence / 'kernel-replay.log')
        if args.stage in ('all', 'comparison'):
            report['comparison'] = compare(project, evidence, args.allow_unsandboxed_local_comparison)
        if args.stage in ('all', 'render'):
            if not args.verso or not args.renderer_packages:
                raise RuntimeError('Rendering requires --verso and --renderer-packages')
            report['render'] = render(project, tools, evidence, args.verso.resolve(),
                                      args.renderer_packages.resolve())
        report['inputs_unchanged'] = before == fingerprints(project)
        if not report['inputs_unchanged']:
            raise RuntimeError('Inputs changed during verification; rerun on the final snapshot')
        report['status'] = 'passed'
    except Exception as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        write(result, report)
    print(f'Passed local {args.stage}: {result}', flush=True)


if __name__ == '__main__':
    main()
