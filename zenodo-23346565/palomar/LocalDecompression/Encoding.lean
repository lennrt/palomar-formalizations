module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

@[expose] public section

/-! Explicit block coding for local edge-label decompression.

The low binary digit stores the orientation advice, so it can be read before
the decoder knows which edges the payload describes.  Mathlib's explicit
`finFunctionFinEquiv` converts the packed integer to fixed-length base-q digits.
The root marker is separate from the q data symbols.
-/
namespace LocalDecompression

/-- Padded edge payload length for a cell of size `s` and degree bound `d`. -/
def payloadLength (d s : ℕ) : ℕ := (d * s + 1) / 2

theorem payloadLength_add_two (d s : ℕ) :
    payloadLength d (s + 2) = payloadLength d s + d := by
  unfold payloadLength
  simp only [Nat.mul_add]
  omega

/-- A general two-step capacity induction, useful for any data alphabet. -/
theorem capacity_from_two_bases (d q s₀ : ℕ) (hs₀ : 1 ≤ s₀)
    (hratio : 2 ^ d ≤ q ^ 2)
    (hbase : 2 ^ (1 + payloadLength d s₀) ≤ q ^ (s₀ - 1))
    (hnext : 2 ^ (1 + payloadLength d (s₀ + 1)) ≤ q ^ s₀) :
    ∀ s, s₀ ≤ s → 2 ^ (1 + payloadLength d s) ≤ q ^ (s - 1) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro hs
    by_cases heq : s = s₀
    · simpa [heq] using hbase
    by_cases heq' : s = s₀ + 1
    · simpa [heq'] using hnext
    have hprev : s₀ ≤ s - 2 := by omega
    have hsmall : s - 2 < s := by omega
    have hp := ih (s - 2) hsmall hprev
    have hsadd : s = (s - 2) + 2 := by omega
    have hexp : s - 1 = (s - 2 - 1) + 2 := by omega
    have hlen : 1 + payloadLength d s =
        (1 + payloadLength d (s - 2)) + d := by
      calc
        1 + payloadLength d s = 1 + payloadLength d ((s - 2) + 2) :=
          congrArg (fun t => 1 + payloadLength d t) hsadd
        _ = (1 + payloadLength d (s - 2)) + d := by
          rw [payloadLength_add_two]
          omega
    calc
      2 ^ (1 + payloadLength d s) =
          2 ^ (1 + payloadLength d (s - 2)) * 2 ^ d := by rw [hlen, pow_add]
      _ ≤ q ^ (s - 2 - 1) * q ^ 2 := Nat.mul_le_mul hp hratio
      _ = q ^ (s - 1) := by rw [← pow_add, ← hexp]

/-- One advice bit and ceil(3s/2) payload bits fit in the non-root trits. -/
theorem cubic_capacity (s : ℕ) (hs : 37 ≤ s) :
    2 ^ (1 + payloadLength 3 s) ≤ 3 ^ (s - 1) := by
  apply capacity_from_two_bases 3 3 37 (by omega) (by norm_num)
    (by norm_num [payloadLength]) (by norm_num [payloadLength]) s hs

/-- Reserving one of the 2^k symbols leaves a uniform multiplicative surplus
over the entropy rate of degree 2k-1. -/
theorem odd_alphabet_ratio (k : ℕ) (hk : 2 ≤ k) :
    9 * 2 ^ (2 * k - 1) ≤ 8 * (2 ^ k - 1) ^ 2 := by
  have ht : 4 ≤ 2 ^ k := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  have hq : (2 ^ k - 1) + 1 = 2 ^ k := by omega
  have hp : 2 * 2 ^ (2 * k - 1) = (2 ^ k) ^ 2 := by
    rw [← pow_succ', ← pow_mul]
    congr 1
    omega
  nlinarith [sq_nonneg (2 ^ k - 4 : ℤ)]

/-- Sixteen non-root symbols supply at least one extra binary bit. -/
theorem odd_alphabet_sixteen (k : ℕ) (hk : 2 ≤ k) :
    2 ^ (8 * (2 * k - 1) + 1) ≤ (2 ^ k - 1) ^ 16 := by
  have hp := Nat.pow_le_pow_left (odd_alphabet_ratio k hk) 8
  simp only [mul_pow, ← pow_mul] at hp
  norm_num at hp
  have hg : 2 * 2 ^ ((2 * k - 1) * 8) ≤ (2 ^ k - 1) ^ 16 := by
    omega
  calc
    2 ^ (8 * (2 * k - 1) + 1) = 2 * 2 ^ ((2 * k - 1) * 8) := by
      rw [pow_add, pow_one, Nat.mul_comm 8 (2 * k - 1)]
      ring
    _ ≤ (2 ^ k - 1) ^ 16 := hg

/-- The explicit threshold used for every odd degree d=2k-1. -/
theorem odd_degree_capacity (k s : ℕ) (hk : 2 ≤ k)
    (hs : 16 * (k + 1) + 1 ≤ s) :
    2 ^ (1 + payloadLength (2 * k - 1) s) ≤ (2 ^ k - 1) ^ (s - 1) := by
  let d := 2 * k - 1
  let q := 2 ^ k - 1
  have hpow := Nat.pow_le_pow_left (odd_alphabet_sixteen k hk) (k + 1)
  have hgain : 2 ^ (8 * d * (k + 1) + k + 1) ≤ q ^ (16 * (k + 1)) := by
    simpa only [d, q, ← pow_mul, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hpow
  have hq : 2 ^ (k - 1) ≤ q := by
    have hp : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hpos : 0 < 2 ^ (k - 1) := by positivity
    dsimp [q]
    omega
  have hratio : 2 ^ d ≤ q ^ 2 := by
    have h := odd_alphabet_ratio k hk
    dsimp [d, q]
    omega
  apply capacity_from_two_bases d q (16 * (k + 1) + 1) (by omega) hratio ?_ ?_ s hs
  · have he : 1 + payloadLength d (16 * (k + 1) + 1) =
        8 * d * (k + 1) + k + 1 := by
      unfold payloadLength
      have hd : d + 1 = 2 * k := by dsimp [d]; omega
      have he : d * (16 * (k + 1) + 1) + 1 =
          2 * (8 * d * (k + 1) + k) := by nlinarith
      rw [he]
      omega
    simpa only [he, Nat.add_sub_cancel] using hgain
  · have he : 1 + payloadLength d (16 * (k + 1) + 1 + 1) =
        (8 * d * (k + 1) + k + 1) + (k - 1) := by
      unfold payloadLength
      have hd : d + 1 = 2 * k := by dsimp [d]; omega
      have he : d * (16 * (k + 1) + 1 + 1) + 1 =
          2 * (8 * d * (k + 1) + d) + 1 := by ring
      rw [he]
      omega
    rw [he, pow_add, pow_succ]
    exact Nat.mul_le_mul hgain hq

/-- Integer representation: advice occupies the least significant bit. -/
def packedValue {m : ℕ} (advice : Fin 2) (payload : Fin (2 ^ m)) : ℕ :=
  2 * payload.val + advice.val

theorem packedValue_lt {m : ℕ} (advice : Fin 2) (payload : Fin (2 ^ m)) :
    packedValue advice payload < 2 ^ (1 + m) := by
  have ha := advice.isLt
  have hp := payload.isLt
  simp only [packedValue, pow_add, pow_one]
  omega

/-- A computable fixed-length base-q representation of advice and payload. -/
def blockEncode {m q k : ℕ} (capacity : 2 ^ (1 + m) ≤ q ^ k)
    (advice : Fin 2) (payload : Fin (2 ^ m)) : Fin k → Fin q :=
  finFunctionFinEquiv.symm
    ⟨packedValue advice payload, (packedValue_lt advice payload).trans_le capacity⟩

/-- Advice decoding does not depend on the payload length or edge ownership. -/
def blockAdvice {q k : ℕ} (word : Fin k → Fin q) : Fin 2 :=
  ⟨(finFunctionFinEquiv word).val % 2, Nat.mod_lt _ (by omega)⟩

/-- Payload decoding is total; unused base-q words are reduced modulo 2^m. -/
def blockPayload {m q k : ℕ} (word : Fin k → Fin q) : Fin (2 ^ m) :=
  ⟨((finFunctionFinEquiv word).val / 2) % (2 ^ m),
    Nat.mod_lt _ (by positivity)⟩

theorem blockEncode_value {m q k : ℕ} (capacity : 2 ^ (1 + m) ≤ q ^ k)
    (advice : Fin 2) (payload : Fin (2 ^ m)) :
    (finFunctionFinEquiv (blockEncode capacity advice payload)).val =
      2 * payload.val + advice.val := by
  simp [blockEncode, packedValue]

@[simp] theorem blockAdvice_encode {m q k : ℕ} (capacity : 2 ^ (1 + m) ≤ q ^ k)
    (advice : Fin 2) (payload : Fin (2 ^ m)) :
    blockAdvice (blockEncode capacity advice payload) = advice := by
  apply Fin.ext
  simp only [blockAdvice, blockEncode_value]
  have ha := advice.isLt
  omega

@[simp] theorem blockPayload_encode {m q k : ℕ} (capacity : 2 ^ (1 + m) ≤ q ^ k)
    (advice : Fin 2) (payload : Fin (2 ^ m)) :
    blockPayload (blockEncode capacity advice payload) = payload := by
  apply Fin.ext
  simp only [blockPayload, blockEncode_value]
  have ha := advice.isLt
  have hp := payload.isLt
  have hdiv : (2 * payload.val + advice.val) / 2 = payload.val := by omega
  rw [hdiv, Nat.mod_eq_of_lt hp]

theorem blockEncode_injective {m q k : ℕ} (capacity : 2 ^ (1 + m) ≤ q ^ k) :
    Function.Injective (fun x : Fin 2 × Fin (2 ^ m) => blockEncode capacity x.1 x.2) := by
  intro a b h
  apply Prod.ext
  · have := congrArg blockAdvice h
    simpa using this
  · have := congrArg (blockPayload (m := m)) h
    simpa using this

/-- The same codec with a literal vector of edge bits as input. -/
def bitBlockEncode {m q k : ℕ} (capacity : 2 ^ (1 + m) ≤ q ^ k)
    (advice : Fin 2) (payload : Fin m → Fin 2) : Fin k → Fin q :=
  blockEncode capacity advice (finFunctionFinEquiv payload)

def bitBlockPayload {m q k : ℕ} (word : Fin k → Fin q) : Fin m → Fin 2 :=
  finFunctionFinEquiv.symm (blockPayload word)

@[simp] theorem bitBlockAdvice_encode {m q k : ℕ} (capacity : 2 ^ (1 + m) ≤ q ^ k)
    (advice : Fin 2) (payload : Fin m → Fin 2) :
    blockAdvice (bitBlockEncode capacity advice payload) = advice := by
  simp [bitBlockEncode]

@[simp] theorem bitBlockPayload_encode {m q k : ℕ} (capacity : 2 ^ (1 + m) ≤ q ^ k)
    (advice : Fin 2) (payload : Fin m → Fin 2) :
    bitBlockPayload (bitBlockEncode capacity advice payload) = payload := by
  simp [bitBlockPayload, bitBlockEncode]

/-- Zero padding in a fixed capacity block, using the chosen edge enumeration. -/
def padBits {n m : ℕ} (_capacity : n ≤ m) (payload : Fin n → Fin 2) (j : Fin m) : Fin 2 :=
  if h : j.val < n then payload ⟨j.val, h⟩ else 0

@[simp] theorem padBits_read {n m : ℕ} (capacity : n ≤ m)
    (payload : Fin n → Fin 2) (j : Fin n) :
    padBits capacity payload (Fin.castLE capacity j) = payload j := by
  simp [padBits, j.isLt]

/-- Padding for arbitrary finite edge sets after a fixed enumeration is supplied. -/
def finitePayload {E : Type*} {n m : ℕ} (enumeration : E ≃ Fin n)
    (capacity : n ≤ m) (payload : E → Fin 2) : Fin m → Fin 2 :=
  padBits capacity (payload ∘ enumeration.symm)

@[simp] theorem finitePayload_read {E : Type*} {n m : ℕ}
    (enumeration : E ≃ Fin n) (capacity : n ≤ m) (payload : E → Fin 2) (e : E) :
    finitePayload enumeration capacity payload (Fin.castLE capacity (enumeration e)) =
      payload e := by
  simp [finitePayload]

@[simp] theorem finitePayload_block_roundtrip {E : Type*} {n m q k : ℕ}
    (enumeration : E ≃ Fin n) (slots : n ≤ m) (capacity : 2 ^ (1 + m) ≤ q ^ k)
    (advice : Fin 2) (payload : E → Fin 2) (e : E) :
    bitBlockPayload (bitBlockEncode capacity advice (finitePayload enumeration slots payload))
      (Fin.castLE slots (enumeration e)) = payload e := by
  simp

/-- Zero is reserved for the root; data symbols are 1,...,q. -/
def markedBlock {m q k : ℕ} (capacity : 2 ^ (1 + m) ≤ q ^ k)
    (advice : Fin 2) (payload : Fin (2 ^ m)) : Option (Fin k) → Fin (q + 1)
  | none => 0
  | some i => (blockEncode capacity advice payload i).succ

theorem markedBlock_zero_iff {m q k : ℕ} (capacity : 2 ^ (1 + m) ≤ q ^ k)
    (advice : Fin 2) (payload : Fin (2 ^ m)) (i : Option (Fin k)) :
    markedBlock capacity advice payload i = 0 ↔ i = none := by
  cases i <;> simp [markedBlock, Fin.ext_iff]

/-- Remove the reserved marker symbol after the cell root has been found.
This is a total decoder, including words which are not valid encodings. -/
def unmarkedBlock {q k : ℕ} (hq : 0 < q) (word : Option (Fin k) → Fin (q + 1)) :
    Fin k → Fin q :=
  fun i => ⟨((word (some i)).val - 1) % q, Nat.mod_lt _ hq⟩

@[simp] theorem unmarkedBlock_markedBlock {m q k : ℕ}
    (capacity : 2 ^ (1 + m) ≤ q ^ k) (hq : 0 < q)
    (advice : Fin 2) (payload : Fin (2 ^ m)) :
    unmarkedBlock hq (markedBlock capacity advice payload) =
      blockEncode capacity advice payload := by
  funext i
  apply Fin.ext
  simpa [unmarkedBlock, markedBlock] using
    Nat.mod_eq_of_lt (blockEncode capacity advice payload i).isLt

@[simp] theorem markedBlock_advice_roundtrip {m q k : ℕ}
    (capacity : 2 ^ (1 + m) ≤ q ^ k) (hq : 0 < q)
    (advice : Fin 2) (payload : Fin (2 ^ m)) :
    blockAdvice (unmarkedBlock hq (markedBlock capacity advice payload)) = advice := by simp

@[simp] theorem markedBlock_payload_roundtrip {m q k : ℕ}
    (capacity : 2 ^ (1 + m) ≤ q ^ k) (hq : 0 < q)
    (advice : Fin 2) (payload : Fin (2 ^ m)) :
    blockPayload (unmarkedBlock hq (markedBlock capacity advice payload)) = payload := by simp

theorem markedBlock_card (s : ℕ) (hs : 1 ≤ s) :
    Fintype.card (Option (Fin (s - 1))) = s := by
  simp only [Fintype.card_option, Fintype.card_fin]
  omega

/-- Small components use every symbol, with no root marker or orientation bit. -/
def plainBlockEncode {m q k : ℕ} (capacity : 2 ^ m ≤ q ^ k)
    (payload : Fin m → Fin 2) : Fin k → Fin q :=
  finFunctionFinEquiv.symm
    ⟨(finFunctionFinEquiv payload).val,
      (finFunctionFinEquiv payload).isLt.trans_le capacity⟩

def plainBlockDecode {m q k : ℕ} (word : Fin k → Fin q) : Fin m → Fin 2 :=
  finFunctionFinEquiv.symm
    ⟨(finFunctionFinEquiv word).val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩

@[simp] theorem plainBlock_roundtrip {m q k : ℕ} (capacity : 2 ^ m ≤ q ^ k)
    (payload : Fin m → Fin 2) :
    plainBlockDecode (plainBlockEncode capacity payload) = payload := by
  apply finFunctionFinEquiv.injective
  simp only [plainBlockDecode, plainBlockEncode, Equiv.apply_symm_apply]
  apply Fin.ext
  exact Nat.mod_eq_of_lt (finFunctionFinEquiv payload).isLt

theorem plain_binary_capacity (edges vertices bits : ℕ) (h : edges ≤ bits * vertices) :
    2 ^ edges ≤ (2 ^ bits) ^ vertices := by
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by omega) h

/-- The code for every sufficiently large subcubic cell uses four vertex states. -/
def cubicBlock (s : ℕ) (hs : 37 ≤ s) (advice : Fin 2)
    (payload : Fin (2 ^ payloadLength 3 s)) : Option (Fin (s - 1)) → Fin 4 :=
  markedBlock (cubic_capacity s hs) advice payload

theorem odd_alphabet_with_marker (k : ℕ) : (2 ^ k - 1) + 1 = 2 ^ k := by
  have h : 0 < 2 ^ k := by positivity
  omega

/-- The marked odd-degree block has precisely k bits at every vertex. -/
def oddDegreeBlock (k s : ℕ) (hk : 2 ≤ k) (hs : 16 * (k + 1) + 1 ≤ s)
    (advice : Fin 2) (payload : Fin (2 ^ payloadLength (2 * k - 1) s)) :
    Option (Fin (s - 1)) → Fin (2 ^ k) :=
  fun i => Fin.cast (odd_alphabet_with_marker k)
    (markedBlock (odd_degree_capacity k s hk hs) advice payload i)

end LocalDecompression
