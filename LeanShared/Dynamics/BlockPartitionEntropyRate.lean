module

public import LeanShared.Dynamics.BlockPartitionEntropy
public import LeanShared.Dynamics.PartitionEntropyRate

/-! Exact entropy-rate scaling for the actual consecutive-block partition.
This is proved from the literal blocking identity and the genuine Fekete
limits, rather than assuming entropy scaling for iterates. -/
public noncomputable section
open Function Filter MeasureTheory
open scoped Topology
namespace LeanShared.ThermodynamicDefinitions.MeasurablePartition
variable {X : Type*} [MeasurableSpace X] {l : ℕ}

set_option maxHeartbeats 800000 in
theorem blockPartition_entropyRate (P : MeasurablePartition (X := X) l)
    (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ]
    (invariant : MeasurePreserving T μ μ) (n : ℕ) (positive : 0 < n) :
    (P.blockPartition T invariant.measurable n).entropyRate (T^[n]) μ =
      (n : ℝ) * P.entropyRate T μ := by
  have times : Tendsto (fun k : ℕ => k * n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    exact hk.trans (Nat.le_mul_of_pos_right k positive)
  have original := ((P.entropyRate_tendsto T μ invariant).comp times).const_mul (n : ℝ)
  have blocked := (P.blockPartition T invariant.measurable n).entropyRate_tendsto
    (T^[n]) μ (invariant.iterate n)
  have same : (fun k : ℕ => (n : ℝ) * (dynamicalEntropy P T μ (k * n) / (k * n : ℕ))) =ᶠ[atTop]
      (fun k : ℕ => dynamicalEntropy (P.blockPartition T invariant.measurable n) (T^[n]) μ k / k) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [P.blockPartition_dynamicalEntropy]
    have nonzeroK : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have nonzeroN : (n : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
    push_cast
    field_simp
  exact tendsto_nhds_unique blocked (original.congr' same)

end LeanShared.ThermodynamicDefinitions.MeasurablePartition
