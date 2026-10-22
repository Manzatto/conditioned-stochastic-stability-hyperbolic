module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Cancellation of an actual integer-order elliptic frequency gain against
polynomial block growth. -/
public section
namespace LeanShared.FrequencyGainCancellation
theorem bound {r E A D S : ℝ} (q : ℕ) (large : 1 ≤ r)
    (nonnegative : 0 ≤ E)
    (gain : r^(2*(q+1))*E ≤ D*(A*r^q)*S) :
    E ≤ (D*A*S)*r⁻¹ := by
  have positive : 0<r := by linarith
  have powers : r^(q+1) ≤ r^(2*(q+1)) :=
    pow_le_pow_right₀ large (by omega)
  have small := (mul_le_mul_of_nonneg_right powers nonnegative).trans gain
  rw [pow_succ] at small
  have scaled : r^q*(r*E) ≤ r^q*(D*A*S) := by nlinarith only [small]
  have once : r*E ≤ D*A*S := (mul_le_mul_iff_right₀ (pow_pos positive q)).mp scaled
  rw [← div_eq_mul_inv,le_div_iff₀ positive]
  simpa only [mul_comm] using once
end LeanShared.FrequencyGainCancellation
