#!/usr/bin/env python3
"""Build and audit the standalone release and run all exact finite programs.

Run with: python3 scripts/verify_release.py
Requires the pinned Lean toolchain, Python 3, and a C++17 compiler.
Independent kernel comparison is run with scripts/verify_comparison.py; see its
--help output. This script checks the recorded comparison input hashes.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
PROGRAMS = ['verify_grid','verify_hypercube','verify_bishop','verify_petersen11',
            'verify_petersen16','verify_fractional','defect_certificates',
            'verify_moments','verify_rectangles','verify_folded_cube12',
            'verify_cube_bounds','verify_folded_cube16','verify_grid_all_orders',
            'grid_detector_census']


def run(command, logfile):
    start = time.monotonic()
    print('Running ' + ' '.join(map(str, command)), flush=True)
    with logfile.open('w') as stream:
        p = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    if p.returncode:
        raise RuntimeError(f'Failed: {command}; inspect {logfile}')
    return round(time.monotonic()-start, 3)


def main():
    if not __debug__:
        raise RuntimeError('Do not optimize away the exact-check assertions.')
    OUT.mkdir(exist_ok=True)
    result = {'status':'running','registered':False,'service_verification':False,
              'toolchain':(ROOT/'lean-toolchain').read_text().strip(),
              'python':sys.version.split()[0]}
    report = OUT/'release.json'
    report.write_text(json.dumps(result, indent=2)+'\n')
    result['build_seconds'] = run(['lake','build'], OUT/'release-build.log')
    declarations = {}
    for name in ['AxiomAudit','ExpansionAudit']:
        source = ROOT/'verification'/(name+'.lean')
        output = OUT/(name+'.log')
        run(['lake','env','lean',str(source)], output)
        text = output.read_text()
        groups = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)
        empty = re.findall(r"'([^']+)' does not depend on any axioms",text)
        if len(groups)+len(empty) != source.read_text().count('#print axioms'):
            raise RuntimeError('Incomplete axiom audit: '+name)
        for declaration in empty: declarations[declaration] = []
        for declaration, body in groups:
            axioms = set(filter(None,(x.strip() for x in body.split(','))))
            if not axioms <= ALLOWED:
                raise RuntimeError('Unapproved axiom for '+declaration)
            declarations[declaration] = sorted(axioms)
    result['audited_declarations'] = declarations
    result['audit_count'] = len(declarations)
    run([sys.executable,'scripts/check_snapshot.py'],OUT/'structure.log')
    target = ROOT/'experiments'/'results'
    target.mkdir(exist_ok=True)
    result['experiments'] = {}
    for name in PROGRAMS:
        output = target/(name+'.json')
        seconds = run([sys.executable,'experiments/'+name+'.py'],output)
        payload = json.loads(output.read_text())
        if not isinstance(payload,dict): raise RuntimeError('Malformed result '+name)
        result['experiments'][name] = {'status':'passed','seconds':seconds,
                'sha256':hashlib.sha256(output.read_bytes()).hexdigest()}
    comparison = json.loads((OUT/'comparison.json').read_text())
    mismatch = [name for name,expected in comparison['input_sha256'].items()
                if not (ROOT/name).is_file() or hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=expected]
    result['comparison_record_status'] = comparison['status']
    result['comparison_input_mismatches'] = mismatch
    result['selected_comparison_declarations'] = comparison['selected_declarations']
    result['local_verification_mode'] = comparison['comparison_sandbox']
    result['status'] = 'passed' if comparison['status']=='passed' and not mismatch else 'comparison_refresh_needed'
    report.write_text(json.dumps(result,indent=2)+'\n')
    print(f"{result['status']}: {report}",flush=True)
    if result['status']!='passed': raise SystemExit(1)


if __name__=='__main__':
    main()
