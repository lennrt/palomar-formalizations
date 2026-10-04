#!/usr/bin/env python3
"""Run the pinned official metadata/source checks for this project and repository snapshot.

Requires PyYAML and a checkout of PalomarRegistry/PalomarSubmission at the
revision below. Pass that checkout with --submission-tools. All sibling
Lean sources are inspected as part of the repository-wide intake requirements.
This is a local preflight, not Palomar service verification or editorial review.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parents[1]
TOOLS_COMMIT = '65f0154ed776cd26c224254aa57b379137f28b0d'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--submission-tools', type=Path, required=True)
    args = parser.parse_args()
    tools = args.submission_tools.resolve()
    revision = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=tools, text=True).strip()
    if revision != TOOLS_COMMIT:
        raise RuntimeError('Use the documented PalomarSubmission revision: ' + TOOLS_COMMIT)
    tracked_changes = subprocess.check_output(
        ['git', 'status', '--porcelain', '--untracked-files=no'], cwd=tools, text=True)
    if tracked_changes.strip():
        raise RuntimeError('The official checker checkout has modified tracked files.')
    sys.path.insert(0, str(tools))
    from scripts.source_requirements import inspect_lean_sources
    from scripts.submission_contract import load_formalization_metadata

    metadata_path = ROOT / 'formalization.yaml'
    metadata = load_formalization_metadata(metadata_path)
    for field in ('authors', 'responsible_maintainers'):
        names = [v if isinstance(v, str) else v['name']
                 for v in metadata['project'][field]]
        if names != ['Lennart Rudolph']:
            raise RuntimeError('Unexpected project attribution: ' + field)
    local, local_issues = inspect_lean_sources(ROOT)
    repository, repository_issues = inspect_lean_sources(REPOSITORY)
    toolchain = (ROOT / 'lean-toolchain').read_text().strip()
    minimum = json.loads((tools / 'toolchains.json').read_text())['minimum']
    if toolchain != 'leanprover/lean4:' + minimum:
        raise RuntimeError('This snapshot must use the checked official minimum toolchain.')
    report = {
        'status': 'passed' if not local_issues and not repository_issues else 'failed',
        'scope': 'project metadata and sources; repository-wide Lean source policy',
        'official_checker_repository': 'https://github.com/PalomarRegistry/PalomarSubmission',
        'official_checker_commit': revision,
        'formalization_sha256': digest(metadata_path),
        'metadata': 'passed',
        'project_authors': ['Lennart Rudolph'],
        'toolchain': toolchain,
        'source_requirements': local,
        'source_errors': [str(issue) for issue in local_issues],
        'repository_wide_source_check': {
            'status': 'blocked' if repository_issues else 'passed',
            'files_checked': repository['files_checked'],
            'issue_count': len(repository_issues),
            'issue_codes': dict(Counter(issue.code for issue in repository_issues)),
            'affected_projects': dict(Counter(
                issue.path.split('/')[0] for issue in repository_issues)),
        },
        'service_verification': False,
        'editorial_review': False,
        'registered': False,
    }
    target = ROOT / 'verification' / 'palomar-preflight.json'
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(f"New project: {report['status']}; {local['files_checked']} Lean files.")
    print(f'Repository-wide source issues: {len(repository_issues)}.')
    if local_issues or repository_issues:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
