import ShellTomography.Grid

/-!
Explicit alternating-boundary sensor placement and integer coefficient formulas.
The definitions are transcribed from the paper; all-order proofs are in UniformRecovery.
-/

namespace ShellTomography

/-- The four unrestricted integer coordinates (a,b,c,d) in the paper kernel formula. -/
structure Params4 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

namespace Params4

def zero : Params4 := ⟨0,0,0,0⟩

def neg (p : Params4) : Params4 := ⟨-p.a,-p.b,-p.c,-p.d⟩

def add (p q : Params4) : Params4 := ⟨p.a+q.a,p.b+q.b,p.c+q.c,p.d+q.d⟩

def smul (k : ℤ) (p : Params4) : Params4 := ⟨k*p.a,k*p.b,k*p.c,k*p.d⟩

def l1 (p : Params4) : ℕ := p.a.natAbs + p.b.natAbs + p.c.natAbs + p.d.natAbs

@[simp] theorem eq_zero_iff (p : Params4) : p = zero ↔ p.a=0 ∧ p.b=0 ∧ p.c=0 ∧ p.d=0 := by
  constructor
  · rintro rfl; simp [zero]
  · rintro ⟨ha,hb,hc,hd⟩
    cases p
    simp_all [zero]

end Params4

/-- Coefficient of q^e at q^j. -/
def monoCoeff (e j : ℕ) : ℤ := if e = j then 1 else 0

/-- Coefficient of (1+q²)q^e. -/
def pairCoeff (e j : ℕ) : ℤ := monoCoeff e j + monoCoeff (e+2) j

/-- Sign (-1)^i. -/
def paritySign (i : ℕ) : ℤ := if Even i then 1 else -1

/-- Row coefficient for odd n, expanded from the odd-order row and parameter formulas in Section 5.2. -/
def oddKernelEntry (n i j : ℕ) (p : Params4) : ℤ :=
  let m := n-1
  if i = 0 then
    -p.a * monoCoeff (m-2) j - p.b * monoCoeff (m-1) j
  else if i = 1 then
    -p.c * monoCoeff 1 j - p.d * monoCoeff 2 j
      + p.a * pairCoeff (m-3) j + p.b * pairCoeff (m-2) j
  else if i = m-1 then
    p.a * monoCoeff 1 j + p.b * monoCoeff 2 j
      - p.c * pairCoeff (m-3) j - p.d * pairCoeff (m-2) j
  else if i = m then
    p.c * monoCoeff (m-2) j + p.d * monoCoeff (m-1) j
  else
    paritySign i *
      (p.c * pairCoeff (i-2) j + p.d * pairCoeff (i-1) j
       - p.a * pairCoeff (m-2-i) j - p.b * pairCoeff (m-1-i) j)

/-- Row coefficient for even n, expanded from the even-order row and parameter formulas in Section 5.2. -/
def evenKernelEntry (n i j : ℕ) (p : Params4) : ℤ :=
  let m := n-1
  if i = 0 then
    -p.d * monoCoeff (m-1) j
  else if i = 1 then
    -p.a * monoCoeff 1 j - p.b * monoCoeff 2 j - p.c * monoCoeff 3 j
      + p.d * monoCoeff (m-2) j + p.d * monoCoeff m j
  else if i = m-1 then
    p.a * monoCoeff (m-3) j + p.b * monoCoeff (m-2) j + p.c * monoCoeff (m-1) j
      - p.d * monoCoeff 0 j - p.d * monoCoeff 2 j
  else if i = m then
    p.d * monoCoeff 1 j
  else
    paritySign i *
      (p.a * pairCoeff (i-2) j + p.b * pairCoeff (i-1) j
       + p.c * pairCoeff i j - p.d * pairCoeff (m-1-i) j)

/-- The explicit n²-vector B_n p. -/
def alternatingKernelVector (n : ℕ) (p : Params4) : SignedConfiguration (Grid n) := fun v =>
  if Odd n then oddKernelEntry n v.1.val v.2.val p
  else evenKernelEntry n v.1.val v.2.val p

/-- There are n-2 sensors, indexed by the interior first coordinate minus one. -/
abbrev AltSensor (n : ℕ) := Fin (n-2)

/-- Alternating boundary vertex associated to sensor k. -/
def altSensorVertex {n : ℕ} (hn : 3 ≤ n) (k : AltSensor n) : Grid n :=
  let i : ℕ := k.val + 1
  let fi : Fin n := ⟨i, by have := k.isLt; omega⟩
  if Odd i then (fi, ⟨0,by omega⟩) else (fi, ⟨n-1,by omega⟩)

/-- Actual Manhattan distance table for the alternating sensors. -/
def altDistance {n : ℕ} (hn : 3 ≤ n) : AltSensor n → Grid n → ℕ :=
  fun k v => manhattan (altSensorVertex hn k) v

/-- Extract the four integer kernel parameters from fixed grid coordinates. -/
def alternatingExtract {n : ℕ} (hn : 6 ≤ n) (z : SignedConfiguration (Grid n)) : Params4 :=
  let m := n-1
  if Odd n then
    ⟨- z (⟨0,by omega⟩,⟨m-2,by omega⟩),
     - z (⟨0,by omega⟩,⟨m-1,by omega⟩),
       z (⟨m,by omega⟩,⟨m-2,by omega⟩),
       z (⟨m,by omega⟩,⟨m-1,by omega⟩)⟩
  else
    ⟨z (⟨2,by omega⟩,⟨0,by omega⟩),
     z (⟨2,by omega⟩,⟨1,by omega⟩),
     z (⟨m-1,by omega⟩,⟨m-1,by omega⟩),
    -z (⟨0,by omega⟩,⟨m-1,by omega⟩)⟩


end ShellTomography
