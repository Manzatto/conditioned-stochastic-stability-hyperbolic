module

public import LeanShared.Analysis.GraphJacobian

/-! Monotonicity of the structural graph-density bound. This lets a uniform
endpoint projection bound replace the pointwise projection norm without
introducing a word-length-dependent constant. -/

public noncomputable section

namespace LeanShared.GraphJacobian

variable {ι : Type*} [Fintype ι]

theorem densityBound_mono {L K : ℝ} (nonnegative : 0 ≤ L) (bound : L ≤ K) :
    densityBound (ι := ι) L ≤ densityBound (ι := ι) K := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact pow_le_pow_left₀ (by positivity)
    (by nlinarith [pow_le_pow_left₀ nonnegative bound 2]) _

end LeanShared.GraphJacobian
