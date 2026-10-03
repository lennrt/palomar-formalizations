#!/usr/bin/env python3
"""Exact finite proof that gamma(Omega_16) = 8, hence xi(Q_16) = 32776.

Not a Lean certificate. Two independently written C++17 programs exhaust every
candidate dominating set of seven classes that contains an isolated selected
class; the dimension-uniform theorem (formal in Lean as
`equalizer_card_lower_bound`, and in the paper as the isolate statement of the
folded-domination theorem) shows that any dominating set with fewer than n/2
classes has such an isolated class. Both programs are first run on dimensions
8 and 12, where the answers are known, as positive and negative controls.

Method 1 (folded_cube_anchored.cpp): four sorted rows + two propagated centres.
Method 2 (folded_cube_pair_audit.cpp): pair-cover decomposition, stars and bars,
literal distances, generic recursion on the last uncovered class.
"""
import hashlib
import json
from math import comb
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def undominated(n, centres):
    return [x for x in range(1 << (n - 1)) if x.bit_count() % 2 == 0
            and all((x ^ c).bit_count() not in (0, n // 2, n) for c in centres)]


def forced_heavy_centres(n, others):
    """Least number of centres of representative weight n/2-2 among `others`
    admissible centres, needed to dominate all weight-two classes."""
    pairs = comb(n, 2)
    per_heavy = comb(n // 2 + 2, 2)
    for heavy in range(others + 1):
        if heavy * per_heavy + (others - heavy) >= pairs:
            return heavy
    return others + 1


def main():
    compiler = shutil.which('c++') or shutil.which('clang++') or shutil.which('g++')
    if not compiler:
        raise RuntimeError('A C++17 compiler is required for the finite audit.')
    threads = str(max(1, min(12, (os.cpu_count() or 4) - 1)))
    sources = {name: ROOT / name for name in
               ('folded_cube_anchored.cpp', 'folded_cube_pair_audit.cpp')}
    runs = {}
    with tempfile.TemporaryDirectory(prefix='folded-cube16-') as directory:
        binaries = {}
        for name, source in sources.items():
            binary = str(Path(directory) / source.stem)
            subprocess.run([compiler, '-O2', '-std=c++17', '-pthread', str(source), '-o', binary],
                           check=True)
            binaries[name] = binary

        def run(name, *arguments):
            output = subprocess.check_output([binaries[name], *map(str, arguments), threads],
                                             text=True)
            return json.loads(output)

        a, p = 'folded_cube_anchored.cpp', 'folded_cube_pair_audit.cpp'
        # Controls in dimension 8: no dominating 3-set; anchored dominating 4-sets exist.
        runs['n8_three_centres'] = run(a, 8, 0, 0)
        runs['n8_four_centres_anchored'] = run(a, 8, 1, 1)
        runs['n8_four_centres_pair_audit'] = run(p, 8, 3, 0)
        assert runs['n8_three_centres']['completions_found'] == 0
        assert runs['n8_four_centres_anchored']['completions_found'] > 0
        assert runs['n8_four_centres_pair_audit']['families_with_completion'] > 0
        # Controls in dimension 12.
        runs['n12_five_centres'] = run(a, 12, 2, 0)
        runs['n12_six_centres'] = run(a, 12, 3, 0)
        runs['n12_six_centres_anchored'] = run(a, 12, 3, 1)
        runs['n12_five_centres_pair_audit'] = run(p, 12, 3, 1)
        runs['n12_six_centres_pair_audit'] = run(p, 12, 3, 2)
        assert runs['n12_five_centres']['completions_found'] == 0
        assert runs['n12_six_centres']['completions_found'] > 0
        assert runs['n12_six_centres_anchored']['completions_found'] == 0
        assert runs['n12_five_centres_pair_audit']['families_with_completion'] == 0
        assert runs['n12_six_centres_pair_audit']['families_with_completion'] == 0
        example = runs['n12_six_centres']['partial_example']
        completions = [c for c in range(1 << 11) if c.bit_count() % 2 == 0
                       and not undominated(12, example + [c])]
        assert completions, 'reported partial example must extend to a dominating 6-set'
        # Dimension 16, seven centres, one of them isolated.
        runs['n16_seven_centres_anchored'] = run(a, 16, 4, 1)
        runs['n16_seven_centres_pair_audit'] = run(p, 16, 4, 2)

    first, second = runs['n16_seven_centres_anchored'], runs['n16_seven_centres_pair_audit']
    assert first['classes'] == 1 << 14 and first['closed_neighbourhood'] == 1 + comb(16, 8) // 2
    assert first['compositions'] == comb(31, 15) == 300_540_195
    assert first['even_row_compositions'] == (comb(31, 15) + 15 * comb(15, 7)) // 16 == 18_789_795
    assert first['row_orbits'] == 104_742
    assert first['second_last_centre_candidates'] == 385_260_636
    assert first['completions_found'] == 0
    assert first['least_uncovered_before_last_centre'] == 564
    assert second['pattern_tuples'] == comb(31, 15)
    assert second['row_families'] == 74_959 and second['forced_weight'] == 6
    assert second['families_with_completion'] == 0
    # arithmetic behind the pair-cover decomposition
    assert forced_heavy_centres(16, 6) == 3 and forced_heavy_centres(12, 4) == 3
    assert forced_heavy_centres(12, 5) == 3 and comb(10, 2) == 45
    # the twelve-dimensional composition count used in the paper
    assert runs['n12_six_centres']['compositions'] == comb(19, 7) == 50_388
    # upper witnesses, checked literally
    prefixes = {n: [(1 << (2 * i)) - 1 for i in range(n // 2)] for n in (8, 12, 16)}
    for n, centres in prefixes.items():
        assert not undominated(n, centres)
    print(json.dumps({
        'status': 'passed', 'arithmetic': 'exact integers',
        'scope': 'complete finite enumeration by two programs, not kernel-checked Lean',
        'theorem_used': 'a dominating set with fewer than n/2 classes has an isolated selected class',
        'source_sha256': {name: hashlib.sha256(path.read_bytes()).hexdigest()
                          for name, path in sources.items()},
        'runs': runs,
        'prefix_upper_witnesses': prefixes,
        'folded_domination_numbers': {'8': 4, '12': 6, '16': 8},
        'cube_equidistant_dimensions': {'8': 132, '12': 2054, '16': 32776},
    }, indent=2))


if __name__ == '__main__':
    main()
