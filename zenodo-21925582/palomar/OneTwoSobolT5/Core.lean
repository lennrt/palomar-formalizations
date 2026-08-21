/-
Paper: Exact Projection Quality of OneTwo Sobol' Sequences at 65,536 Points
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925582
Preprint published: 2026-08-14. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

/-!
# Exact `t=5` certificate for OneTwo Sobol dimensions 25--28 at `m=16`

The four lists below are the rows of the top-left `16 x 16` generator matrices
obtained from one-based dimensions 25--28 of the published OneTwo table.  A
composition of `q` selects the first `d_i` rows from matrix `i`, with
`d_1+d_2+d_3+d_4=q`.  The standard digital-net rank criterion says that
`t ≤ 16-q` exactly when every such selected family is independent over `F₂`.

Independence is decided by a deterministic 16-column XOR row reduction.  The
upper-bound certificate checks all 364 weak compositions of 11.  The
lower-bound witness is the composition `(0,3,3,6)` and dependency mask
`0xD2F`.
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

namespace Comp4

def total (x : Comp4) : Nat := x.a + x.b + x.c + x.d

end Comp4

/-- All weak compositions of `n` into four ordered parts. -/
def comps4 (n : Nat) : List Comp4 :=
  (List.range (n + 1)).flatMap fun a =>
    let r₁ := n - a
    (List.range (r₁ + 1)).flatMap fun b =>
      let r₂ := r₁ - b
      (List.range (r₂ + 1)).map fun c =>
        { a := a, b := b, c := c, d := r₂ - c }

/-- Generator rows for one-based dimension 25. -/
def rows25 : List Nat :=
  [0xD38B, 0x9E16, 0x25A4, 0xC0C8,
   0x6F10, 0x55A0, 0x7CC0, 0x8B80,
   0x3900, 0x2E00, 0x0400, 0x0800,
   0xF000, 0xE000, 0xC000, 0x8000]

/-- Generator rows for one-based dimension 26. -/
def rows26 : List Nat :=
  [0xAF05, 0xC566, 0x9664, 0x17C8,
   0x7610, 0xB0E0, 0xADC0, 0xA280,
   0xD900, 0xEE00, 0xAC00, 0x4800,
   0xF000, 0xE000, 0xC000, 0x8000]

/-- Generator rows for one-based dimension 27. -/
def rows27 : List Nat :=
  [0x86A7, 0xD08A, 0x3444, 0xD878,
   0x9050, 0x7B20, 0x1AC0, 0xEC80,
   0xD900, 0x6E00, 0x9400, 0x5800,
   0x7000, 0xA000, 0xC000, 0x8000]

/-- Generator rows for one-based dimension 28. -/
def rows28 : List Nat :=
  [0xBFF5, 0xE9BA, 0xB354, 0xE718,
   0x8750, 0x7AE0, 0x3BC0, 0x3280,
   0x7900, 0xAE00, 0x6C00, 0x1800,
   0xB000, 0x2000, 0xC000, 0x8000]

/-- First 16 direction columns for one-based dimension 25. -/
def directions25 : List Nat :=
  [0x80000000, 0xC0000000, 0x60000000, 0x90000000,
   0x48000000, 0x24000000, 0x12000000, 0xB7000000,
   0xAD800000, 0xC9400000, 0x6E600000, 0x4BD00000,
   0xC6880000, 0x2ACC0000, 0x9E0E0000, 0xD10F0000]

/-- First 16 direction columns for one-based dimension 26. -/
def directions26 : List Nat :=
  [0x80000000, 0x40000000, 0xE0000000, 0x10000000,
   0x08000000, 0x64000000, 0x76000000, 0x17000000,
   0xD2800000, 0xB9400000, 0xFA600000, 0x82F00000,
   0x3C880000, 0x8F6C0000, 0x48DE0000, 0xE7EF0000]

/-- First 16 direction columns for one-based dimension 27. -/
def directions27 : List Nat :=
  [0x80000000, 0xC0000000, 0xA0000000, 0x50000000,
   0x18000000, 0x94000000, 0x3A000000, 0xC3000000,
   0x04800000, 0x86400000, 0xA1600000, 0x17D00000,
   0x7EB80000, 0x254C0000, 0x55DA0000, 0xD9A70000]

/-- First 16 direction columns for one-based dimension 28. -/
def directions28 : List Nat :=
  [0x80000000, 0x40000000, 0xA0000000, 0x50000000,
   0xF8000000, 0xC4000000, 0xAE000000, 0xC7000000,
   0xFA800000, 0xBF400000, 0x98600000, 0xC6F00000,
   0xA7980000, 0xF7EC0000, 0x54A20000, 0xF84B0000]

/-- Transpose the first 16 direction columns at one output-bit position. -/
def rowFromDirections (directions : List Nat) (outputRow : Nat) : Nat :=
  (List.range 16).foldl (fun acc column =>
    if ((directions.getD column 0 / 2 ^ (31 - outputRow)) % 2 = 1)
    then acc + 2 ^ column else acc) 0

/-- The first 16 packed generator rows obtained from direction columns. -/
def rowsFromDirections (directions : List Nat) : List Nat :=
  (List.range 16).map (rowFromDirections directions)

/-- Source-fidelity check from all 64 pinned direction numbers to all 64 rows. -/
theorem source_directions_to_rows :
    rowsFromDirections directions25 = rows25 ∧
    rowsFromDirections directions26 = rows26 ∧
    rowsFromDirections directions27 = rows27 ∧
    rowsFromDirections directions28 = rows28 := by
  decide

/-- Stack the leading rows selected by a four-part composition. -/
def stackedRows (x : Comp4) : List Nat :=
  rows25.take x.a ++ rows26.take x.b ++ rows27.take x.c ++ rows28.take x.d

/-- XOR the subset selected by the low bits of `mask`. -/
def xorSubset : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, mask =>
      let tail := xorSubset xs (mask / 2)
      if mask % 2 = 1 then Nat.xor x tail else tail

/-- Insert one packed row into a 16-column XOR echelon basis.  A missing result
means that the row reduces to zero and is dependent on the earlier rows. -/
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

/-- Rank criterion for every four-part composition of a fixed total. -/
def allIndependentAt (q : Nat) : Bool :=
  (comps4 q).all fun x => independent (stackedRows x)

/-- The threshold rank condition at total `16-t0`, with its mathematical
domain `t0 ≤ 16` made explicit so truncated natural subtraction cannot create
spurious propositions.  The paper proves its equivalence with `t ≤ t0`; the
exact certificate below evaluates every candidate `t0=0,1,2,3,4,5` used in
the conclusion. -/
def tLeByRank (t0 : Nat) : Prop :=
  t0 ≤ 16 ∧ allIndependentAt (16 - t0) = true

/-- The explicit rank-deficient composition for total 12. -/
def witness : Comp4 := { a := 0, b := 3, c := 3, d := 6 }

/-- The dependency mask selects rows 1,2,3 of dimension 26; rows 1,3 of
27; and rows 3,5,6 of dimension 28. -/
def witnessMask : Nat := 0xD2F

/-- Sanity check for the weak-composition enumerator. -/
theorem compositions_11_count : (comps4 11).length = 364 := by
  decide

/-- The total-11 enumerator has no duplicate compositions. -/
theorem compositions_11_nodup : (comps4 11).Nodup := by
  decide

/-- Every total-11 record has the stated coordinate sum. -/
theorem compositions_11_totals :
    (comps4 11).all (fun x => x.total == 11) = true := by
  decide

/-- The corresponding total-12 search contains 455 distinct compositions. -/
theorem compositions_12_count : (comps4 12).length = 455 := by
  decide

/-- The total-12 enumerator has no duplicate compositions. -/
theorem compositions_12_nodup : (comps4 12).Nodup := by
  decide

/-- Every total-12 record has the stated coordinate sum. -/
theorem compositions_12_totals :
    (comps4 12).all (fun x => x.total == 12) = true := by
  decide

/-- Every enumerated composition through the largest threshold has the
advertised coordinate sum. -/
theorem compositions_13_to_16_totals :
    (comps4 13).all (fun x => x.total == 13) = true ∧
    (comps4 14).all (fun x => x.total == 14) = true ∧
    (comps4 15).all (fun x => x.total == 15) = true ∧
    (comps4 16).all (fun x => x.total == 16) = true := by
  decide

/-- No selected stack is shortened by `List.take` in the total-11 and
total-12 certificate ranges. -/
theorem selected_stack_lengths :
    (comps4 11).all (fun x => (stackedRows x).length == 11) = true ∧
    (comps4 12).all (fun x => (stackedRows x).length == 12) = true := by
  decide

/-- Every one of the 364 total-11 composition matrices has full row rank. -/
theorem all_total_11_independent : allIndependentAt 11 = true := by
  decide

/-- Therefore the digital-net rank criterion certifies `t ≤ 5`. -/
theorem t_le_five_certificate : tLeByRank 5 := by
  simpa [tLeByRank] using all_total_11_independent

/-- The lower-bound witness consists of exactly 12 selected rows. -/
theorem witness_row_count : (stackedRows witness).length = 12 := by
  decide

/-- The exact 12-row list fixes the mask-to-row ordering convention. -/
theorem witness_rows_exact : stackedRows witness =
    [0xAF05, 0xC566, 0x9664,
     0x86A7, 0xD08A, 0x3444,
     0xBFF5, 0xE9BA, 0xB354, 0xE718, 0x8750, 0x7AE0] := by
  decide

/-- The selected witness rows have a nontrivial XOR dependency. -/
theorem witness_dependency : xorSubset (stackedRows witness) witnessMask = 0 := by
  decide

/-- Consequently, not all total-12 composition matrices have full row rank. -/
theorem some_total_12_dependent : allIndependentAt 12 = false := by
  decide

/-- A dependent threshold stack also excludes `t ≤ 3`. -/
theorem some_total_13_dependent : allIndependentAt 13 = false := by
  decide

/-- A dependent threshold stack also excludes `t ≤ 2`. -/
theorem some_total_14_dependent : allIndependentAt 14 = false := by
  decide

/-- A dependent threshold stack also excludes `t ≤ 1`. -/
theorem some_total_15_dependent : allIndependentAt 15 = false := by
  decide

/-- A dependent threshold stack also excludes `t ≤ 0`. -/
theorem some_total_16_dependent : allIndependentAt 16 = false := by
  decide

/-- Therefore the digital-net rank criterion does not certify `t ≤ 4`. -/
theorem not_t_le_four_certificate : ¬ tLeByRank 4 := by
  intro h
  have hTrue : allIndependentAt 12 = true := by
    simpa [tLeByRank] using h
  rw [some_total_12_dependent] at hTrue
  cases hTrue

theorem not_t_le_three_certificate : ¬ tLeByRank 3 := by
  intro h
  have hTrue : allIndependentAt 13 = true := by
    simpa [tLeByRank] using h
  rw [some_total_13_dependent] at hTrue
  cases hTrue

theorem not_t_le_two_certificate : ¬ tLeByRank 2 := by
  intro h
  have hTrue : allIndependentAt 14 = true := by
    simpa [tLeByRank] using h
  rw [some_total_14_dependent] at hTrue
  cases hTrue

theorem not_t_le_one_certificate : ¬ tLeByRank 1 := by
  intro h
  have hTrue : allIndependentAt 15 = true := by
    simpa [tLeByRank] using h
  rw [some_total_15_dependent] at hTrue
  cases hTrue

theorem not_t_le_zero_certificate : ¬ tLeByRank 0 := by
  intro h
  have hTrue : allIndependentAt 16 = true := by
    simpa [tLeByRank] using h
  rw [some_total_16_dependent] at hTrue
  cases hTrue

/-- The exact finite-field certificate evaluates the upper threshold and every
smaller candidate value, without appealing to an unstated monotonicity step. -/
theorem exact_t_five_certificate :
    tLeByRank 5 ∧
    ¬ tLeByRank 4 ∧
    ¬ tLeByRank 3 ∧
    ¬ tLeByRank 2 ∧
    ¬ tLeByRank 1 ∧
    ¬ tLeByRank 0 := by
  exact ⟨t_le_five_certificate,
    not_t_le_four_certificate,
    not_t_le_three_certificate,
    not_t_le_two_certificate,
    not_t_le_one_certificate,
    not_t_le_zero_certificate⟩

/-- The dependency can also be read as the explicit eight-row XOR identity
printed in the paper. -/
theorem explicit_eight_row_xor :
    Nat.xor 0xAF05
      (Nat.xor 0xC566
        (Nat.xor 0x9664
          (Nat.xor 0x86A7
            (Nat.xor 0x3444
              (Nat.xor 0xB354
                (Nat.xor 0x8750 0x7AE0)))))) = 0 := by
  decide

end OneTwoSobolT5
