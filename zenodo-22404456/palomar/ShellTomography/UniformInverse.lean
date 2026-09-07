import ShellTomography.UniformNecessity

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial
local notation "q" => (T 1 : LP)
local notation "D" => (1-T 2 : LP)

def tridiagonal {m : ℕ} (hm : 1 ≤ m) (L : Fin (m+1) → LP) (i : Fin (m+1)) : LP :=
  if h₀ : i.val = 0 then L i - q * L ⟨1,by omega⟩
  else if hl : i.val = m then L i - q * L ⟨m-1,by omega⟩
  else (1+T 2)*L i - q * (L ⟨i.val-1,by have := i.isLt; omega⟩ +
    L ⟨i.val+1,by have := i.isLt; omega⟩)

theorem tridiagonal_zero {m : ℕ} (hm : 1 ≤ m) (L : Fin (m+1) → LP)
    (hz : ∀ i, tridiagonal hm L i = 0) : L = 0 := by
  have step (i : ℕ) (hi : i < m) : L ⟨i,by omega⟩ = q * L ⟨i+1,by omega⟩ := by
    induction i with
    | zero =>
      have h := hz 0
      simpa [tridiagonal,sub_eq_zero] using h
    | succ i ih =>
      have hp := ih (by omega)
      have h := hz ⟨i+1,by omega⟩
      simp only [tridiagonal,show i+1 ≠ 0 by omega,show i+1 ≠ m by omega,
        dite_false,Nat.add_sub_cancel] at h
      rw [hp] at h
      have he : (1+T 2 : LP)*L ⟨i+1,by omega⟩ -
          q*(q*L ⟨i+1,by omega⟩+L ⟨i+1+1,by omega⟩) =
          L ⟨i+1,by omega⟩ - q*L ⟨i+1+1,by omega⟩ := by laurent_ring
      rw [he] at h
      exact sub_eq_zero.mp h
  have hend : L (Fin.last m) = 0 := by
    have h := hz (Fin.last m)
    simp only [tridiagonal,Fin.val_last,show m ≠ 0 by omega,dite_false,dite_true] at h
    have hs := step (m-1) (by omega)
    have e : m-1+1=m := by omega
    simp only [e] at hs
    rw [hs] at h
    change L (Fin.last m) - q*(q*L (Fin.last m)) = 0 at h
    have hh : L (Fin.last m) - q*(q*L (Fin.last m)) = D*L (Fin.last m) := by laurent_ring
    rw [hh] at h
    exact (mul_eq_zero.mp h).resolve_left D_ne_zero
  have all (k : ℕ) : ∀ i : Fin (m+1), m-i.val=k → L i = 0 := by
    induction k with
    | zero =>
      intro i hi
      have h : i=Fin.last m := Fin.ext (by change i.val=m; have := i.isLt; omega)
      simpa [h] using hend
    | succ k ih =>
      intro i hi
      have him : i.val < m := by omega
      have hs := step i.val him
      have hn := ih ⟨i.val+1,by omega⟩ (by change m-(i.val+1)=k; omega)
      simpa [hn] using hs
  funext i
  exact all (m-i.val) i rfl

theorem tridiagonal_injective {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (tridiagonal hm) := by
  intro L M h
  have hz : ∀ i, tridiagonal hm (L-M) i=0 := by
    intro i
    have hh := congrFun h i
    unfold tridiagonal at hh ⊢
    split_ifs at hh ⊢ <;> dsimp only [Pi.sub_apply] <;> linear_combination hh
  exact sub_eq_zero.mp (tridiagonal_zero hm (L-M) hz)

theorem tridiagonal_response {m : ℕ} (hm : 1 ≤ m) (F : Fin (m+1) → LP) :
    tridiagonal hm (fun i => rowResponse F i.val) = fun i => D*F i := by
  funext i
  unfold tridiagonal
  split_ifs with h₀ hl
  · have hi : i=0 := Fin.ext h₀
    subst i
    exact green_first F
  · have hi : i=Fin.last m := Fin.ext hl
    subst i
    simpa only [Fin.val_last,Nat.cast_sub (show 1 ≤ m by omega),Nat.cast_one] using green_last F
  · have h := green_row F i
    simpa only [Nat.cast_sub (show 1 ≤ i.val by omega),Nat.cast_add,Nat.cast_one] using h

end ShellTomography.Uniform
