module

public import LeanShared.Dynamics.FiniteRelativeEntropy
import Mathlib.Tactic.Positivity

/-! The actual finite relative-entropy variational inequality, proved by
normalizing the exponentially tilted reference probability. Zero atoms of
the tested law are retained. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.FiniteRelativeEntropy
variable {I : Type*} [Fintype I] [Nonempty I]

set_option maxHeartbeats 1000000 in
theorem test_function_bound (p q f : I → ℝ) (nonnegative : ∀ i, 0 ≤ p i)
    (positiveQ : ∀ i, 0 < q i) (totalP : ∑ i, p i = 1) :
    (∑ i, p i * f i) ≤ (∑ i, p i * Real.log (p i / q i)) +
      Real.log (∑ i, q i * Real.exp (f i)) := by
  let Z := ∑ i, q i * Real.exp (f i)
  have positiveZ : 0 < Z := Finset.sum_pos
    (fun i _ => mul_pos (positiveQ i) (Real.exp_pos _)) Finset.univ_nonempty
  let tilted := fun i => q i * Real.exp (f i) / Z
  have positiveTilt (i : I) : 0 < tilted i :=
    div_pos (mul_pos (positiveQ i) (Real.exp_pos _)) positiveZ
  have totalTilt : ∑ i, tilted i = 1 := by
    simp only [tilted, div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ positiveZ.ne'
  have score := score_nonpos p tilted nonnegative positiveTilt totalP totalTilt
  have expand (i : I) : p i * Real.log (tilted i / p i) =
      p i * f i - p i * Real.log (p i / q i) - p i * Real.log Z := by
    by_cases zero : p i = 0
    · simp only [zero, zero_mul, sub_self]
    have positiveP : 0 < p i := lt_of_le_of_ne (nonnegative i) (Ne.symm zero)
    have logTilt : Real.log (tilted i) = Real.log (q i) + f i - Real.log Z := by
      dsimp only [tilted]
      rw [Real.log_div (mul_pos (positiveQ i) (Real.exp_pos _)).ne' positiveZ.ne',
        Real.log_mul (positiveQ i).ne' (Real.exp_ne_zero _), Real.log_exp]
    rw [Real.log_div (positiveTilt i).ne' positiveP.ne', logTilt,
      Real.log_div positiveP.ne' (positiveQ i).ne']
    ring
  simp_rw [expand, Finset.sum_sub_distrib] at score
  rw [← Finset.sum_mul, totalP, one_mul] at score
  linarith

end LeanShared.FiniteRelativeEntropy
