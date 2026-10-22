module

public import LeanShared.Analysis.UniformWeakResolventBound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Actual weak resolvent difference estimates from the first perturbative
resolvent identity and the proved weak-resolvent absorption estimate. -/

public section
open ContinuousLinearMap
namespace LeanShared.WeakResolventDifference
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A weak-resolvent estimate converts weak perturbation control into a bound
on the actual weak resolvent difference; strong perturbations need only be bounded. -/
theorem norm_le (P Q : E →L[ℂ] E) (i : E →L[ℂ] W) (z : ℂ)
    (hP : z ∈ resolventSet ℂ P) (hQ : z ∈ resolventSet ℂ Q)
    (η C J τ K : ℝ) (hη : 0 ≤ η) (hC : 0 ≤ C) (hJ : 0 ≤ J) (hτ : 0 ≤ τ) (hK : 0 ≤ K)
    (weakQ : ∀ x, ‖i ((resolvent Q z) x)‖ ≤ η * ‖x‖ + C * ‖i x‖)
    (strongPerturbation : ‖P - Q‖ ≤ J)
    (weakPerturbation : ‖i.comp (P - Q)‖ ≤ τ)
    (normP : ‖resolvent P z‖ ≤ K) :
    ‖i.comp (resolvent P z - resolvent Q z)‖ ≤ (η * J + C * τ) * K := by
  let Δ := P - Q
  have difference : resolvent P z - resolvent Q z = resolvent Q z * Δ * resolvent P z := by
    have reversed : resolvent Q z - resolvent P z = -(resolvent Q z * Δ * resolvent P z) := by
      rw [spectrum.resolvent_sub_resolvent hQ hP]
      change resolvent Q z * (Q - P) * resolvent P z = _
      rw [← neg_sub P Q, mul_neg, neg_mul]
    calc
      _ = -(resolvent Q z - resolvent P z) := (neg_sub _ _).symm
      _ = _ := by rw [reversed, neg_neg]
  have coef : 0 ≤ η * J + C * τ := add_nonneg (mul_nonneg hη hJ) (mul_nonneg hC hτ)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg coef hK)
  intro x
  change ‖i ((resolvent P z - resolvent Q z) x)‖ ≤ _
  rw [difference, mul_apply_eq_comp, mul_apply_eq_comp]
  let y := (resolvent P z) x
  have hs : ‖Δ y‖ ≤ J * ‖y‖ := (Δ.le_opNorm y).trans
    (mul_le_mul_of_nonneg_right strongPerturbation (norm_nonneg y))
  have hw : ‖i (Δ y)‖ ≤ τ * ‖y‖ := ((i.comp Δ).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right weakPerturbation (norm_nonneg y))
  have hy : ‖y‖ ≤ K * ‖x‖ := ((resolvent P z).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right normP (norm_nonneg x))
  have inner : ‖i ((resolvent Q z) (Δ y))‖ ≤ (η * J + C * τ) * ‖y‖ :=
    (weakQ (Δ y)).trans ((add_le_add
      (mul_le_mul_of_nonneg_left hs hη) (mul_le_mul_of_nonneg_left hw hC)).trans_eq (by ring))
  exact inner.trans ((mul_le_mul_of_nonneg_left hy coef).trans_eq (by ring))

end LeanShared.WeakResolventDifference
