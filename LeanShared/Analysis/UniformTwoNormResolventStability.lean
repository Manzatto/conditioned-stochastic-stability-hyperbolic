module

public import LeanShared.Analysis.UniformTwoNormSpectralShift
public import LeanShared.Analysis.TwoNormPerturbedResolvent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The uniform actual KL resolvent-stability estimate on bounded outer
annuli, proved by weak-resolvent/Peetre absorption. -/

public section
open ContinuousLinearMap
namespace LeanShared.UniformTwoNormResolventStability
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Uniform actual resolvent stability under a small weak-norm perturbation.
The strong perturbation is only bounded, not required to tend to zero.
No compactness or perturbative spectral source contract is assumed. -/
theorem exists_bound (Q : E →L[ℂ] E) (i : E →L[ℂ] W)
    (α M C D Cw r outer bound L : ℝ)
    (hα : 0 ≤ α) (hM : 0 ≤ M) (hC : 0 ≤ C) (hD : 0 ≤ D) (hCw : 0 ≤ Cw)
    (hr : α < r) (houter : 0 ≤ outer) (hbound : 0 ≤ bound) (hL : 0 ≤ L)
    (strongQ : ∀ n x, ‖(Q ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * M ^ n * ‖i x‖)
    (weakQ : ∀ n x, ‖i ((Q ^ n) x)‖ ≤ Cw * M ^ n * ‖i x‖) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 ≤ K ∧ ∀ P : E →L[ℂ] E, ‖P‖ ≤ bound →
      (∀ n x, ‖(P ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * M ^ n * ‖i x‖) →
      ‖i.comp (P - Q)‖ ≤ τ → ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ outer →
      z ∈ resolventSet ℂ Q → ‖resolvent Q z‖ ≤ L →
      (Function.Injective (z • (1 : E →L[ℂ] E) - P) →
        DenseRange (z • (1 : E →L[ℂ] E) - P)) →
      z ∈ resolventSet ℂ P ∧ ‖resolvent P z‖ ≤ K := by
  obtain ⟨A, B, hA, hB, peetre⟩ := UniformTwoNormSpectralShift.exists_annulus_bound
    i α M C D r outer bound hα hM hD hr houter hbound
  let J := bound + ‖Q‖
  obtain ⟨η, hη, hηsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 4) (A * J)
  obtain ⟨Cweak, hCweak, weakResolver⟩ := UniformWeakResolventBound.exists_bound Q i
    α M C D Cw r outer L hα hM hC hD hCw hr houter hL strongQ weakQ η hη
  obtain ⟨τ, hτ, hτsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 4) (A * Cweak)
  have small : A * (η * J + Cweak * τ) < 1 := by nlinarith
  let K := (A * ‖i‖ * L + B) / (1 - A * (η * J + Cweak * τ))
  have hK : 0 ≤ K := by dsimp only [K]; exact div_nonneg (by positivity) (sub_pos.mpr small).le
  refine ⟨τ, K, hτ, hK, fun P hP growth hpert z hlow hhigh hres hnorm noResidual => ?_⟩
  have strongPerturbation : ‖P - Q‖ ≤ J :=
    (norm_sub_le _ _).trans (add_le_add hP le_rfl)
  have pointPeetre : ∀ x, ‖x‖ ≤ A * ‖i x‖ + B * ‖(z • (1 : E →L[ℂ] E) - P) x‖ := by
    intro x
    have h := peetre P hP growth z hlow hhigh x
    simpa only [sub_apply, smul_apply, one_apply_eq_self, norm_sub_rev] using h
  exact TwoNormPerturbedResolvent.invertible P Q i z hres A B L η Cweak J τ
    hA hB hL hη.le hCweak hnorm (weakResolver z hlow hhigh hres hnorm)
    pointPeetre strongPerturbation hpert small noResidual

end LeanShared.UniformTwoNormResolventStability
