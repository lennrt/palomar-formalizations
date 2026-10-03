#!/usr/bin/env python3
"""Check the public source package, pinned dependencies, and proof-source layout.

Run with: python3 scripts/check_snapshot.py
This structural check does not execute Lean or the independent kernels.
"""
import json
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
errors, warnings = [], []
required = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'Challenge.lean',
            'Solution.lean', 'comparator.json', 'formalization.yaml']
for name in required:
    if not (ROOT / name).is_file():
        errors.append(f'missing {name}')
licence = re.compile(r'^(license|licence|copying|unlicense|ofl)(\.(md|markdown|txt))?$', re.I)
REPOSITORY = ROOT.parents[1]
licenses = [p.name for p in REPOSITORY.iterdir() if p.is_file() and licence.fullmatch(p.name)]
if licenses != ['LICENSE']:
    errors.append(f'expected one root LICENSE, found {licenses}')
if (ROOT / 'lakefile.lean').exists():
    errors.append('both Lake configuration formats present')
size = 0
source_count = 0
def source_entries():
    for directory, dirs, files in os.walk(ROOT, followlinks=False):
        dirs[:] = [name for name in dirs if name not in {'.git', '.lake'}]
        for name in dirs + files:
            yield Path(directory)/name

for p in source_entries():
    rel = p.relative_to(ROOT)
    if any(part in {'.git', '.lake'} for part in rel.parts):
        continue
    if p.is_symlink():
        errors.append(f'symbolic link: {rel}')
        continue
    if not p.is_file():
        continue
    data = p.read_bytes()
    size += len(data)
    if data.startswith(b'version https://git-lfs.github.com/spec/v1'):
        errors.append(f'Git LFS pointer: {rel}')
    if p.suffix in {'.olean','.ilean','.a','.bc','.dll','.dylib','.o','.obj','.so','.trace'}:
        errors.append(f'compiled artifact outside .lake: {rel}')
    if p.suffix != '.lean':
        continue
    source_count += 1
    text = data.decode('utf-8')
    lines = len(text.splitlines())
    if lines > 10000:
        errors.append(f'{rel}: {lines} lines exceeds 10000')
    if p.name != 'lakefile.lean' and not re.match(r'^\s*module\b', text):
        errors.append(f'{rel}: missing leading module header')
    if p.name == 'Challenge.lean':
        if lines > 1000 or len(data) > 100*1024:
            errors.append('Challenge exceeds hard size limit')
        elif lines > 300 or len(data) > 32*1024:
            warnings.append(f'Challenge readability warning: {lines} lines, {len(data)} bytes')
        imports = re.findall(r'^\s*(?:public\s+)?import\s+([^\s]+)', text, re.M)
        if any(not (i == 'Mathlib' or i.startswith('Mathlib.') or i == 'Std' or i.startswith('Std.')) for i in imports):
            errors.append(f'Challenge imports a non-allowlisted project: {imports}')
    else:
        # Strip nested comments and strings before scanning forbidden proof tokens.
        tokens = re.findall(r'/\-|\-/|--[^\n]*|"(?:\\.|[^"\\])*"|\b(?:sorry|admit|axiom|native_decide|unsafe|Lean\.ofReduceBool)\b', text)
        depth = 0
        for token in tokens:
            if token == '/-': depth += 1
            elif token == '-/': depth = max(0, depth-1)
            elif depth == 0 and not token.startswith(('--','"')):
                errors.append(f'{rel}: forbidden proof token {token}')
if size > 500*1024*1024:
    errors.append(f'snapshot exceeds 500 MiB: {size} bytes')
manifest_path = ROOT/'lake-manifest.json'
if manifest_path.exists():
    manifest = json.loads(manifest_path.read_text())
    for p in manifest['packages']:
        if p.get('type') == 'git':
            if not re.fullmatch('[0-9a-f]{40}', p['rev']):
                errors.append(f'dependency {p["name"]}: unpinned revision')
            if not re.fullmatch(r'https://github\.com/[^/]+/[^/]+/?', p['url']):
                errors.append(f'dependency {p["name"]}: noncanonical URL')
config_path = ROOT/'comparator.json'
if config_path.exists():
    config = json.loads(config_path.read_text())
    required_keys = {'challenge_module','solution_module','theorem_names','permitted_axioms'}
    allowed_keys = required_keys | {'definition_names','enable_nanoda'}
    if not required_keys <= config.keys() or config.keys()-allowed_keys:
        errors.append('Comparator keys invalid')
    if not config.get('theorem_names'):
        errors.append('Comparator theorem list empty')
    if set(config.get('permitted_axioms',[]))-{'propext','Classical.choice','Quot.sound'}:
        errors.append('Comparator allows a nonstandard axiom')
    if config.get('challenge_module') == config.get('solution_module'):
        errors.append('Challenge and Solution must differ')
for warning in warnings: print('WARNING:', warning)
for error in errors: print('ERROR:', error)
print(json.dumps({'source_files':source_count,'source_snapshot_bytes':size,
                  'errors':len(errors),'warnings':len(warnings),
                  'registered':False,'service_verification':False}, indent=2))
raise SystemExit(bool(errors))
