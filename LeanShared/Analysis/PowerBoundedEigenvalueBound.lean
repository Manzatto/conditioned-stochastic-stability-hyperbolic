module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! A nonzero eigenvector of a uniformly power-bounded operator has
eigenvalue of modulus at most one, by its actual geometric orbit.
-/

public section
namespace LeanShared.PowerBoundedEigenvalueBound
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eigenvalue_norm_le_one (T : E →L[ℂ] E) (C : ℝ)
    (powerBound : ∀ n : ℕ, ‖T ^ n‖ ≤ C) (v : E) (nonzero : v ≠ 0) (z : ℂ)
    (eigen : T v = z • v) : ‖z‖ ≤ 1 := by
  have orbit (n : ℕ) : (T ^ n) v = (z ^ n) • v := by
    induction n with
    | zero => simp only [pow_zero, one_smul]; rfl
    | succ n induction =>
      rw [pow_succ']
      change T ((T ^ n) v) = _
      rw [induction, map_smul, eigen, smul_smul, pow_succ]
  have powers (n : ℕ) : ‖z‖ ^ n ≤ C := by
    have bound := (ContinuousLinearMap.le_opNorm (T ^ n) v).trans
      (mul_le_mul_of_nonneg_right (powerBound n) (norm_nonneg v))
    rw [orbit, norm_smul, norm_pow] at bound
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr nonzero)).mp bound
  by_contra large
  obtain ⟨n, growth⟩ := pow_unbounded_of_one_lt C (lt_of_not_ge large)
  linarith [powers n]

end LeanShared.PowerBoundedEigenvalueBound
