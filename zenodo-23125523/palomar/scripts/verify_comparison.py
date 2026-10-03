#!/usr/bin/env python3
"""Run the bundled Comparator and both kernels used by current Palomar.

Default: use Comparator's Linux Bubblewrap sandbox. On an author-controlled macOS
checkout, the explicit local option runs inside the invoking environment instead;
that is a mathematical local check, not Palomar's isolated service verification.
No network submission, publication, or registry action is performed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs():
    paths = [p for p in ROOT.rglob('*.lean')
             if not any(part in {'.lake', '.git'} for part in p.relative_to(ROOT).parts)]
    paths += [ROOT/name for name in ('lean-toolchain','lakefile.toml',
                                    'lake-manifest.json','comparator.json')]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--allow-unsandboxed-local-comparison', action='store_true',
                        help='Explicitly use the documented local mode; never service evidence.')
    args = parser.parse_args()
    if args.allow_unsandboxed_local_comparison and platform.system() != 'Darwin':
        raise RuntimeError('The local exception in this script is restricted to macOS.')
    before = inputs()
    prefix = Path(subprocess.check_output(['lake','env','lean','--print-prefix'],
                                         cwd=ROOT,text=True).strip())
    bins = {name: prefix/'bin'/name for name in
            ('lake','lean','leanexport','leanchecker','nanoda_bin','con-ron')}
    if any(not p.is_file() for p in bins.values()):
        raise RuntimeError('The pinned toolchain does not contain all required checkers.')
    config = json.loads((ROOT/'comparator.json').read_text())
    config.pop('enable_nanoda', None)
    config['external_kernels'] = {'nanoda':[str(bins['nanoda_bin'])],
                                  'con-ron':[str(bins['con-ron'])]}
    local = ROOT/'.lake'/'local-verification'
    local.mkdir(parents=True, exist_ok=True)
    config_path = local/'comparator.json'
    config_path.write_text(json.dumps(config,indent=2)+'\n')
    output = ROOT/'verification'
    output.mkdir(exist_ok=True)
    result = {'status':'running', 'registered':False, 'service_verification':False,
              'host':platform.system(),
              'comparison_sandbox':'disabled_local_mode' if args.allow_unsandboxed_local_comparison
                                    else 'bubblewrap',
              'toolchain':(ROOT/'lean-toolchain').read_text().strip(),
              'tool_sha256':{n:digest(p) for n,p in bins.items()},
              'selected_declarations':len(config['theorem_names']),
              'configuration':config, 'input_sha256':before}
    result_path = output/'comparison.json'
    result_path.write_text(json.dumps(result,indent=2)+'\n')
    command = ['lake','comparator','--config',str(config_path)]
    if args.allow_unsandboxed_local_comparison:
        command.append('--inadvisably-no-sandbox')
    result['command'] = command
    started = time.monotonic()
    print('Running the pinned Comparator with Lean, NanoDa, and con-ron.',flush=True)
    with (output/'comparison.log').open('w') as stream:
        proc = subprocess.run(command,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
    result['seconds'] = round(time.monotonic()-started,3)
    result['exit_code'] = proc.returncode
    result['inputs_unchanged'] = before == inputs()
    result['status'] = 'passed' if proc.returncode == 0 and result['inputs_unchanged'] else 'failed'
    result_path.write_text(json.dumps(result,indent=2)+'\n')
    print(f"{result['status']}: {result_path}",flush=True)
    if result['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
