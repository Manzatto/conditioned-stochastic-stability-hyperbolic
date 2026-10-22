module

public import LeanShared.Analysis.ResolventFiniteExpansion
import all LeanShared.Analysis.TwoNormSpectralShift
public import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Weak-norm bounds for actual resolvents from finite expansions and genuine
weak/strong power estimates. These are quantitative KL foundations, not
assumed perturbative-resolvent contracts. -/

public section
open ContinuousLinearMap
namespace LeanShared.TwoNormResolventWeakBound
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Weak norm of the actual finite power-difference polynomial. -/
theorem powerSum_bound (T : E →L[ℂ] E) (i : E →L[ℂ] W) (M C : ℝ)
    (growth : ∀ k x, ‖i ((T ^ k) x)‖ ≤ C * M ^ k * ‖i x‖)
    (z : ℂ) (n : ℕ) (x : E) :
    ‖i ((TwoNormSpectralShift.powerSum T z n) x)‖ ≤
      (∑ k ∈ Finset.range n, ‖z‖ ^ (n - 1 - k) * (C * M ^ k)) * ‖i x‖ := by
  have point (k : ℕ) : (T ^ k * (z • (1 : E →L[ℂ] E)) ^ (n - 1 - k)) x =
      z ^ (n - 1 - k) • (T ^ k) x := by
    simp only [smul_pow, one_pow, mul_apply_eq_comp, smul_apply, one_apply_eq_self, map_smul]
  simp only [TwoNormSpectralShift.powerSum, sum_apply, map_sum, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [point, map_smul, norm_smul, norm_pow]
  exact (mul_le_mul_of_nonneg_left (growth k x) (pow_nonneg (norm_nonneg z) _)).trans_eq (by ring)

/-- A finite expansion separates a small strong contribution from a finite
weak contribution in the actual resolvent. No perturbation theorem is assumed. -/
theorem resolvent_bound (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (α M C D Cw : ℝ)
    (strong : ∀ k x, ‖(T ^ k) x‖ ≤ C * α ^ k * ‖x‖ + D * M ^ k * ‖i x‖)
    (weak : ∀ k x, ‖i ((T ^ k) x)‖ ≤ Cw * M ^ k * ‖i x‖)
    (z : ℂ) (hz : z ≠ 0) (hres : z ∈ resolventSet ℂ T) (n : ℕ) (x : E) :
    ‖i ((resolvent T z) x)‖ ≤
      (‖i‖ * ‖resolvent T z‖ * C) * (α / ‖z‖) ^ n * ‖x‖ +
      ((‖i‖ * ‖resolvent T z‖ * D) * (M / ‖z‖) ^ n +
        (∑ k ∈ Finset.range n, ‖z‖ ^ (n - 1 - k) * (Cw * M ^ k)) / ‖z‖ ^ n) * ‖i x‖ := by
  have expansion := congrArg (fun Q : E →L[ℂ] E => Q x)
    (ResolventFiniteExpansion.formula T z hz hres n)
  change (resolvent T z) x = (z ^ n)⁻¹ •
    ((resolvent T z) ((T ^ n) x) + (TwoNormSpectralShift.powerSum T z n) x) at expansion
  have term : ‖i ((resolvent T z) ((T ^ n) x))‖ ≤
      (‖i‖ * ‖resolvent T z‖) *
        (C * α ^ n * ‖x‖ + D * M ^ n * ‖i x‖) := by
    calc
      _ ≤ ‖i‖ * ‖(resolvent T z) ((T ^ n) x)‖ := i.le_opNorm _
      _ ≤ ‖i‖ * (‖resolvent T z‖ * ‖(T ^ n) x‖) :=
        mul_le_mul_of_nonneg_left ((resolvent T z).le_opNorm _) (norm_nonneg i)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (strong n x) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    _ = (‖z‖ ^ n)⁻¹ *
        ‖i ((resolvent T z) ((T ^ n) x)) + i ((TwoNormSpectralShift.powerSum T z n) x)‖ := by
      conv_lhs => rw [expansion]
      rw [map_smul, map_add, norm_smul, norm_inv, norm_pow]
    _ ≤ (‖z‖ ^ n)⁻¹ *
        ((‖i‖ * ‖resolvent T z‖) * (C * α ^ n * ‖x‖ + D * M ^ n * ‖i x‖) +
          (∑ k ∈ Finset.range n, ‖z‖ ^ (n - 1 - k) * (Cw * M ^ k)) * ‖i x‖) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
        (add_le_add term (powerSum_bound T i M Cw weak z n x))) (by positivity)
    _ = _ := by simp only [div_eq_mul_inv]; ring

end LeanShared.TwoNormResolventWeakBound
