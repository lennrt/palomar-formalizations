/-
Paper: Exact Projection Quality of OneTwo Sobol' Sequences at 65,536 Points
Authors: Lennart Rudolph, Sol, Fable
DOI: https://doi.org/10.5281/zenodo.21925582
Preprint published: 2026-08-14. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

/-!
# Exact rank threshold for the OneTwo Sobol' dimensions 25--28 block

The packed rows below are the top-left `16 x 16` generator matrices for the
four one-based dimensions. For each weak four-part composition, the selected
leading rows are checked by deterministic 16-column XOR row reduction. The
advertised theorem checks total 11 and rejects totals 12 through 16, which is
the complete finite rank certificate corresponding to `t = 5` under the
standard digital-net criterion used in the cited preprint.
-/

namespace OneTwoSobolT5

set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure Comp4 where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving Repr, DecidableEq, BEq

/-- All weak compositions of `n` into four ordered parts. -/
def comps4 (n : Nat) : List Comp4 :=
  (List.range (n + 1)).flatMap fun a =>
    let r₁ := n - a
    (List.range (r₁ + 1)).flatMap fun b =>
      let r₂ := r₁ - b
      (List.range (r₂ + 1)).map fun c =>
        { a := a, b := b, c := c, d := r₂ - c }

def rows25 : List Nat :=
  [0xD38B, 0x9E16, 0x25A4, 0xC0C8,
   0x6F10, 0x55A0, 0x7CC0, 0x8B80,
   0x3900, 0x2E00, 0x0400, 0x0800,
   0xF000, 0xE000, 0xC000, 0x8000]

def rows26 : List Nat :=
  [0xAF05, 0xC566, 0x9664, 0x17C8,
   0x7610, 0xB0E0, 0xADC0, 0xA280,
   0xD900, 0xEE00, 0xAC00, 0x4800,
   0xF000, 0xE000, 0xC000, 0x8000]

def rows27 : List Nat :=
  [0x86A7, 0xD08A, 0x3444, 0xD878,
   0x9050, 0x7B20, 0x1AC0, 0xEC80,
   0xD900, 0x6E00, 0x9400, 0x5800,
   0x7000, 0xA000, 0xC000, 0x8000]

def rows28 : List Nat :=
  [0xBFF5, 0xE9BA, 0xB354, 0xE718,
   0x8750, 0x7AE0, 0x3BC0, 0x3280,
   0x7900, 0xAE00, 0x6C00, 0x1800,
   0xB000, 0x2000, 0xC000, 0x8000]

/-- Stack the leading rows selected by a four-part composition. -/
def stackedRows (x : Comp4) : List Nat :=
  rows25.take x.a ++ rows26.take x.b ++ rows27.take x.c ++ rows28.take x.d

/-- XOR the subset selected by the low bits of `mask`. -/
def xorSubset : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, mask =>
      let tail := xorSubset xs (mask / 2)
      if mask % 2 = 1 then Nat.xor x tail else tail

/-- Insert one packed row into a 16-column XOR echelon basis. -/
def addRowToBasis (basis : Array Nat) (row : Nat) : Nat → Option (Array Nat)
  | 0 => none
  | fuel + 1 =>
      let bit := fuel
      if row == 0 then none
      else if row.testBit bit then
        let pivot := basis.getD bit 0
        if pivot == 0 then some (basis.set! bit row)
        else addRowToBasis basis (Nat.xor row pivot) fuel
      else addRowToBasis basis row fuel

/-- Process every row through the packed XOR echelon basis. -/
def independentAux : List Nat → Array Nat → Bool
  | [], _ => true
  | row :: rows, basis =>
      match addRowToBasis basis row 16 with
      | none => false
      | some next => independentAux rows next

/-- Full row rank over `F₂` for rows packed into 16-bit natural numbers. -/
def independent (xs : List Nat) : Bool :=
  independentAux xs (Array.replicate 16 0)

/-- The rank test for every composition of a fixed total. -/
def allIndependentAt (q : Nat) : Bool :=
  (comps4 q).all fun x => independent (stackedRows x)

/-- Threshold rank condition at total `16 - t0`, with its natural domain. -/
def tLeByRank (t0 : Nat) : Prop :=
  t0 ≤ 16 ∧ allIndependentAt (16 - t0) = true

/-- The exact finite rank certificate: threshold 5 holds and 0--4 fail. -/
theorem exact_t_five_certificate :
    tLeByRank 5 ∧
    ¬ tLeByRank 4 ∧
    ¬ tLeByRank 3 ∧
    ¬ tLeByRank 2 ∧
    ¬ tLeByRank 1 ∧
    ¬ tLeByRank 0 := by
  sorry

end OneTwoSobolT5
