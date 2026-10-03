#!/usr/bin/env python3
"""Exact finite proof by exhaustive coordinate orbits; not a Lean certificate.

Two C++17 implementations enumerate every normalized five-center cover type.
The first computes the exact minimum; the second independently checks the lower
bound with stars-and-bars enumeration and literal distance tests. Python checks
counts, an extremal witness, and the six-prefix upper bound independently.
"""
import hashlib
import json
from math import comb
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def missing(centers):
    return [x for x in range(1 << 11) if x.bit_count() % 2 == 0
            and all((x ^ c).bit_count() not in (0, 6, 12) for c in centers)]


def main():
    source = ROOT / 'folded_cube_orbits.cpp'
    compiler = shutil.which('c++') or shutil.which('clang++') or shutil.which('g++')
    if not compiler:
        raise RuntimeError('A C++17 compiler is required for the complete finite audit.')
    with tempfile.TemporaryDirectory(prefix='folded-cube-audit-') as directory:
        binary = str(Path(directory) / 'audit')
        subprocess.run([compiler, '-O2', '-std=c++17', str(source), '-o', binary], check=True)
        reports = [json.loads(subprocess.check_output([binary, mode], text=True))
                   for mode in ('bitset', 'literal')]
    compositions = comb(27, 15)
    even_compositions = (compositions + 15 * comb(13, 7)) // 16
    for report in reports:
        assert report['compositions'] == compositions == 17_383_860
        assert report['even_row_compositions'] == even_compositions == 1_088_100
    assert reports[0]['minimum_uncovered_classes'] == 20
    assert reports[1]['verified_uncovered_lower_bound'] == 20
    witness = reports[0]['witness_centers']
    uncovered = missing(witness)
    assert len(uncovered) == 20
    counts = reports[0]['witness_pattern_counts']
    assert len(counts) == 16 and sum(counts) == 12
    reconstructed = [0, 0, 0, 0]
    coordinate = 0
    for pattern, count in enumerate(counts):
        for _ in range(count):
            for row in range(4):
                reconstructed[row] |= ((pattern >> row) & 1) << coordinate
            coordinate += 1
    assert [0] + reconstructed == witness
    upper = [(1 << (2 * i)) - 1 for i in range(6)]
    assert not missing(upper)
    print(json.dumps({
        'status': 'passed', 'arithmetic': 'exact integers',
        'scope': 'complete finite orbit enumeration, not kernel-checked Lean',
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'methods': reports, 'witness_uncovered_representatives': uncovered,
        'six_center_upper_witness': upper,
        'folded_domination_number': 6, 'cube_equidistant_dimension': 2054,
    }, indent=2))


if __name__ == '__main__':
    main()
