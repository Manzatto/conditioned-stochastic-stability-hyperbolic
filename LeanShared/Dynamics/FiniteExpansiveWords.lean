module

public import LeanShared.Dynamics.FiniteExpansiveCylinders
public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Data.Fintype.Card

/-! A fixed coarse alphabet counts arbitrarily fine separated orbit sets
with only a finite padding of the observation horizon. This is the finite
combinatorial estimate needed for pressure finiteness under expansivity. -/
public noncomputable section
open Function Set
namespace LeanShared.FiniteExpansiveWords
variable {X J : Type*} [MetricSpace X]

private theorem forward_rebase (T : X ≃ₜ X) (j i N : ℕ) (x : X) :
    (T : X → X)^[j] ((T : X → X)^[i] x)=
      (T : X → X)^[j+i+N] ((T.symm : X → X)^[N] x) := by
  have cancel : (T : X → X)^[N] ((T.symm : X → X)^[N] x)=x := T.right_inv.iterate N x
  rw [iterate_add_apply, cancel, iterate_add_apply]

private theorem backward_rebase (T : X ≃ₜ X) (j i N : ℕ) (hj : j ≤ N) (x : X) :
    (T.symm : X → X)^[j] ((T : X → X)^[i] x)=
      (T : X → X)^[i+N-j] ((T.symm : X → X)^[N] x) := by
  have rebase : (T : X → X)^[i] x=
      (T : X → X)^[i+N] ((T.symm : X → X)^[N] x) := by
    have cancel : (T : X → X)^[N] ((T.symm : X → X)^[N] x)=x := T.right_inv.iterate N x
    rw [iterate_add_apply,cancel]
  calc
    _ = (T.symm : X → X)^[j]
        ((T : X → X)^[i+N] ((T.symm : X → X)^[N] x)) := congrArg _ rebase
    _ = (T.symm : X → X)^[j] ((T : X → X)^[j]
        ((T : X → X)^[i+N-j] ((T.symm : X → X)^[N] x))) := by
      rw [←iterate_add_apply]
      congr 2
      omega
    _ = _ := T.left_inv.iterate j _

/-- The finite word starts N steps before the initial observation. -/
def word (T : X ≃ₜ X) (label : X → J) (n N : ℕ) (x : X) : Fin (n+2*N+1) → J :=
  fun k => label ((T : X → X)^[k.val] ((T.symm : X → X)^[N] x))

theorem separated_card_le [Fintype J] (T : X ≃ₜ X) (label : X → J)
    (c ε : ℝ) (N : ℕ)
    (mesh : ∀ x y, label x=label y → dist x y ≤ c)
    (detects : ∀ x y, (∀ j ≤ N,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → dist x y < ε)
    (n : ℕ) (s : Finset X) (separated : ThermodynamicDefinitions.Separated T univ n ε s) :
    s.card ≤ (Fintype.card J)^(n+2*N+1) := by
  have injective : Function.Injective (fun x : s => word T label n N x.val) := by
    intro x y equal
    apply Subtype.ext
    by_contra different
    obtain ⟨i,hi,far⟩ := separated.2 x.val x.property y.val y.property different
    have near := detects ((T : X → X)^[i] x.val) ((T : X → X)^[i] y.val) (by
      intro j hj
      constructor
      · rw [forward_rebase T j i N,forward_rebase T j i N]
        apply mesh
        exact congrFun equal ⟨j+i+N,by omega⟩
      · rw [backward_rebase T j i N hj,backward_rebase T j i N hj]
        apply mesh
        exact congrFun equal ⟨i+N-j,by omega⟩)
    exact (not_lt_of_ge far) near
  have card := Fintype.card_le_of_injective _ injective
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using card

end LeanShared.FiniteExpansiveWords
