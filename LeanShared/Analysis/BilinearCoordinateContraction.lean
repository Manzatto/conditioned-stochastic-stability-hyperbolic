module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith

/-! Contraction for a named positive form becomes the exact operator
contraction in coordinates orthonormal for that form. -/
public section
namespace LeanShared.BilinearCoordinateContraction
variable {P Q H K : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

theorem bound (g : H →L[ℝ] H →L[ℝ] ℝ) (k : K →L[ℝ] K →L[ℝ] ℝ)
    (e : P ≃L[ℝ] H) (f : Q ≃L[ℝ] K) (D : H ≃L[ℝ] K)
    (source : ∀ v, g (e v) (e v) = ‖v‖ ^ 2)
    (target : ∀ v, k (f v) (f v) = ‖v‖ ^ 2)
    (a : ℝ) (nonnegative : 0 ≤ a)
    (contraction : ∀ v, k (D v) (D v) ≤ a ^ 2 * g v v) :
    ‖((e.trans D).trans f.symm).toContinuousLinearMap‖ ≤ a := by
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro v
  change ‖f.symm (D (e v))‖ ≤ a * ‖v‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg nonnegative (norm_nonneg v))).mp
  have estimate := contraction (e v)
  rw [source v] at estimate
  rw [← target (f.symm (D (e v))), f.apply_symm_apply]
  nlinarith

end LeanShared.BilinearCoordinateContraction
