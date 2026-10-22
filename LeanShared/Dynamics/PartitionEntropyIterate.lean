module

public import LeanShared.Dynamics.SampledOrbitEntropy
public import LeanShared.Dynamics.PartitionEntropyRate

/-! The entropy rate of an actual partition sampled under T^n is bounded
by n times its original rate. All limits are the proved invariant Fekete
limits and the finite-time comparison is literal observation sampling. -/
public noncomputable section
open Function Filter MeasureTheory
open scoped Topology
namespace LeanShared.ThermodynamicDefinitions.MeasurablePartition
variable {X : Type*} [MeasurableSpace X] {l : ℕ}

set_option maxHeartbeats 800000 in
theorem entropyRate_iterate_le (P : MeasurablePartition (X := X) l)
    (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ]
    (invariant : MeasurePreserving T μ μ) (n : ℕ) (positive : 0 < n) :
    P.entropyRate (T^[n]) μ ≤ (n : ℝ) * P.entropyRate T μ := by
  have times : Tendsto (fun k : ℕ => k * n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    exact hk.trans (Nat.le_mul_of_pos_right k positive)
  have original := ((P.entropyRate_tendsto T μ invariant).comp times).const_mul (n : ℝ)
  have sampled := P.entropyRate_tendsto (T^[n]) μ (invariant.iterate n)
  apply le_of_tendsto_of_tendsto sampled original
  filter_upwards [eventually_ge_atTop 1] with k hk
  have nonzeroK : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have nonzeroN : (n : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  have compare := div_le_div_of_nonneg_right
    (P.dynamicalEntropy_iterate_le T invariant.measurable μ n k positive) (Nat.cast_nonneg k)
  convert compare using 1
  dsimp only [Function.comp_apply]
  push_cast
  field_simp

end LeanShared.ThermodynamicDefinitions.MeasurablePartition
