module

public import Mathlib

@[expose] public section

namespace ShellObservability.BishopBoundaryCount
open Finset

abbrev Square (N : ℕ) := Fin (N+1) × Fin (N+1)
def boundary {N : ℕ} (v : Square N) : Prop :=
  v.1.val = 0 ∨ v.2.val = 0 ∨ v.1.val = N ∨ v.2.val = N
instance {N : ℕ} (v : Square N) : Decidable (boundary v) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def flip {N : ℕ} (v : Square N) : Square N := (v.1, v.2.rev)

lemma flip_involutive (N : ℕ) : Function.Involutive (@flip N) := by
  intro v
  simp [flip]

lemma flip_boundary {N : ℕ} (v : Square N) : boundary (flip v) ↔ boundary v := by
  have hv := v.2.isLt
  simp only [flip, boundary, Fin.val_rev]
  omega

lemma flip_color {N : ℕ} (hN : N % 2 = 1) (v : Square N) :
    (v.1.val + v.2.val) % 2 = 0 ↔ ((flip v).1.val + (flip v).2.val) % 2 ≠ 0 := by
  have hv := v.2.isLt
  simp only [flip, Fin.val_rev]
  omega

lemma boundary_card (N : ℕ) (hN : 0 < N) :
    ((univ : Finset (Square N)).filter boundary).card = 4*N := by
  let inner : Finset (Fin (N+1)) := (univ.erase 0).erase (Fin.last N)
  have hlast : (Fin.last N : Fin (N+1)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last,Fin.val_zero] at this
    omega
  have hc : inner.card = N-1 := by
    simp [inner, Finset.card_erase_of_mem, hlast]
  have hi : ((univ : Finset (Square N)).filter (fun v => ¬boundary v)) = inner ×ˢ inner := by
    ext v
    simp only [inner, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_erase, ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, and_true]
    unfold boundary
    tauto
  have hp := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Square N))) boundary
  rw [hi, Finset.card_product, hc] at hp
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hp
  have hsub : N-1+1=N := by omega
  nlinarith

/-- On an even-sided board, each checkerboard color has exactly twice the
maximum coordinate many boundary squares. -/
theorem even_boundary_card (N : ℕ) (hN : N % 2 = 1) :
    ((univ : Finset (Square N)).filter
      (fun v => boundary v ∧ (v.1.val+v.2.val)%2=0)).card = 2*N := by
  let B : Finset (Square N) := univ.filter boundary
  have hp := Finset.card_filter_add_card_filter_not (s := B)
    (fun v : Square N => (v.1.val+v.2.val)%2=0)
  have heq : (B.filter (fun v => (v.1.val+v.2.val)%2=0)).card =
      (B.filter (fun v => ¬(v.1.val+v.2.val)%2=0)).card := by
    apply Finset.card_bijective (@flip N) (flip_involutive N).bijective
    intro v
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and,
      flip_boundary]
    exact and_congr Iff.rfl (flip_color hN v)
  have hb : B.card = 4*N := boundary_card N (by omega)
  rw [heq,hb] at hp
  have hf : B.filter (fun v => (v.1.val+v.2.val)%2=0) =
      (univ : Finset (Square N)).filter (fun v => boundary v ∧ (v.1.val+v.2.val)%2=0) := by
    ext v
    simp [B]
  rw [← hf]
  omega

end ShellObservability.BishopBoundaryCount
