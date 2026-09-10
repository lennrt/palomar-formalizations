#!/usr/bin/env python3
"""Build this standalone project and audit actual Lean axiom reports.

This is a local verification command, not a Palomar registration command.
Python 3.11+ and the pinned Lean/lake toolchain are required.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def files():
    return sorted(p for p in ROOT.rglob("*") if p.is_file()
                  and not {".lake", ".verification", ".git", "__pycache__"}.intersection(p.relative_to(ROOT).parts))


def input_hashes():
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in files() if p.suffix in (".lean", ".toml", ".py", ".yaml", ".cff") or p.name in
            ("lean-toolchain", "lake-manifest.json", "comparator.json", "game-comparator.json",
             "formalization.yaml", "tool-pins.json", "selection-map.json", "library-sources.json",
             "proof-sources.json", "declarations.json", "supplementary-results.json")}


def strip_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1; i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i); i = len(text) if end < 0 else end
        else:
            out.append(text[i]); i += 1
    assert not depth, "Unclosed Lean comment"
    return "".join(out)


def imports(module):
    p = ROOT / (module.replace(".", "/") + ".lean")
    return re.findall(r"^import\s+(\S+)", strip_comments(p.read_text()), re.M) if p.exists() else []


def closure(module):
    seen, todo = set(), [module]
    while todo:
        m = todo.pop()
        if m not in seen:
            seen.add(m); todo.extend(imports(m))
    return seen


def static_checks():
    cfg = json.loads((ROOT / "comparator.json").read_text())
    game = json.loads((ROOT / "verification/game-comparator.json").read_text())
    assert len(cfg["theorem_names"]) == len(set(cfg["theorem_names"])) == 39
    assert len(game["theorem_names"]) == len(set(game["theorem_names"])) == 24
    mapping = json.loads((ROOT / "verification/selection-map.json").read_text())["mapping"]
    declarations = json.loads((ROOT / "verification/declarations.json").read_text())
    assert list(mapping) == [d["declaration"] for d in declarations]
    assert len(mapping) == 39 and list(mapping.values()) == cfg["theorem_names"]
    assert sum(old != new for old, new in mapping.items()) == 12
    assert all(d["selected_declaration"] == mapping[d["declaration"]] for d in declarations)
    supplementary = json.loads((ROOT / "verification/supplementary-results.json").read_text())["declarations"]
    excluded = {"ZombieMain.diamond_ring_sensor_bound",
                "ZombieDamage.Graph.involution_blocks_recovery", "PalomarVerified.central_pair_sensor"}
    assert {d["selected_declaration"] for d in supplementary} == excluded
    assert not excluded.intersection(cfg["theorem_names"])
    assert not set(mapping).intersection(d["declaration"] for d in supplementary)
    assert set(game["theorem_names"]) <= set(mapping) | {d["declaration"] for d in supplementary}
    assert cfg["challenge_module"] == "Challenge" and cfg["solution_module"] == "Solution"
    assert game["challenge_module"] == "GameChallenge" and game["solution_module"] == "ZombieDamage"
    for c in (cfg, game):
        assert c.get("enable_nanoda") is True and set(c["permitted_axioms"]) == ALLOWED
        assert not c.get("definition_names")
    assert (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.32.0"
    lake = tomllib.loads((ROOT / "lakefile.toml").read_text())
    assert lake["name"] == "zombie_damage_formalization" and lake["version"] == "1.0.0"
    assert lake["require"] == [{"name": "mathlib", "git": "https://github.com/leanprover-community/mathlib4.git", "rev": "v4.32.0"}]
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    assert manifest["name"] == lake["name"]
    for p in manifest["packages"]:
        assert p["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", p["rev"])
        assert p["url"].startswith("https://github.com/")
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    assert mathlib["rev"] == "81a5d257c8e410db227a6665ed08f64fea08e997"
    origins = json.loads((ROOT / "verification/proof-sources.json").read_text())["sha256"]
    assert len(origins) == 132
    for name, digest in origins.items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
    supplied = json.loads((ROOT / "verification/library-sources.json").read_text())["sha256"]
    assert len(supplied) == 135
    for name, digest in supplied.items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
    expected_holes = {"Challenge.lean": 39, "GameChallenge.lean": 24}
    actual_holes = {}
    lean = [p for p in files() if p.suffix == ".lean"]
    forbidden = r"\b(?:admit|axiom|native_decide|unsafe)\b|Lean\.ofReduceBool|implemented_by"
    for p in lean:
        name = p.relative_to(ROOT).as_posix(); code = strip_comments(p.read_text())
        assert not re.search(forbidden, code), name
        n = len(re.findall(r"\bsorry\b", code))
        assert n == expected_holes.get(name, 0), (name, n)
        if n: actual_holes[name] = n
    assert actual_holes == expected_holes
    assert not {"Challenge", "MainChallenge", "GameChallenge"}.intersection(closure("Solution"))
    assert imports("GameChallenge") == ["Std"]
    assert imports("Challenge") == [
        "Std", "Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph",
        "Mathlib.Combinatorics.SimpleGraph.Finite", "Mathlib.Data.Real.Basic",
        "Mathlib.Data.Finset.Max", "Mathlib.Tactic"]
    challenge = (ROOT / "Challenge.lean").read_text()
    assert len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 100 * 1024
    assert not any(m.startswith(("ZombieDamage", "ZombieMain")) for m in closure("Challenge"))
    assert not re.search(r"\b(?:shellCount|SameShellData|Recovers|DiamondRing|diamondVertex|central_pair_sensor|involution_blocks_recovery|diamond_ring_sensor_bound)\b",
                         strip_comments(challenge)), "Unselected sensing interface in Challenge"
    audit = re.findall(r"#print axioms\s+(\S+)", (ROOT / "verification/Audit.lean").read_text())
    assert len(audit) == len(set(audit)) == 276
    assert set(mapping) <= set(audit)
    assert set(cfg["theorem_names"]) <= set(audit)
    return {"passed": True, "selected_declarations": 39, "independent_challenge_statements": 39,
            "independent_game_statements": 24,
            "selected_transparent_presentation_wrappers": 12,
            "total_transparent_presentation_wrappers": 13,
            "supplementary_sensing_results": 3,
            "original_library_files_unchanged": 132, "lean_files": len(lean),
            "supplied_library_files_unchanged": 135,
            "proof_holes": 0, "challenge_holes": actual_holes, "path_dependencies": 0,
            "challenge_lines": len(challenge.splitlines()), "challenge_bytes": len(challenge.encode())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=ROOT / ".verification/lean")
    parser.add_argument("--static-only", action="store_true")
    args = parser.parse_args()
    out = args.out.resolve(); out.mkdir(parents=True, exist_ok=True)
    result = {"kernel_checked": False, "registered": False}

    def run(cmd, log):
        r = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / log).write_text(r.stdout)
        if r.returncode: raise RuntimeError(f"Exit {r.returncode}: {out / log}")
        return r.stdout

    try:
        result["static"] = static_checks()
        result["input_hashes"] = input_hashes()
        if not args.static_only:
            version = run(["lake", "env", "lean", "--version"], "version.log")
            assert re.search(r"version 4\.32\.0(?:\W|$)", version)
            run(["lake", "build"], "build.log")
            report = run(["lake", "env", "lean", "verification/Audit.lean"], "axioms.log")
            expected = re.findall(r"#print axioms\s+(\S+)", (ROOT / "verification/Audit.lean").read_text())
            got = re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)", report)
            assert set(got) == set(expected), "Missing or unexpected axiom reports"
            blocks = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", report, re.S)
            axioms = {s.strip() for b in blocks for s in b.split(",") if s.strip()}
            assert not axioms - ALLOWED, sorted(axioms - ALLOWED)
            assert input_hashes() == result["input_hashes"], "Inputs changed during verification"
            result.update(kernel_checked=True, audited_declarations=len(expected), found_axioms=sorted(axioms))
        result["exit_code"] = 0
    except (AssertionError, RuntimeError, OSError) as e:
        result.update(exit_code=1, reason=str(e))
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "input_hashes"}, indent=2))
    return result["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
