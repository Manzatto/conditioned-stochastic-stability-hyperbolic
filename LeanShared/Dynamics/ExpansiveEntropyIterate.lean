module

public import LeanShared.Dynamics.BlockPartitionEntropyRate
public import LeanShared.Dynamics.PartitionEntropyIterate
public import LeanShared.Dynamics.ExpansiveGeneratorEntropy
public import LeanShared.Dynamics.SmallBoundaryPartition

/-! Actual compact expansive entropy scales exactly under positive
iterates. Both inequalities follow from finite observation sampling and
consecutive-block coding; the finite generator is constructed internally. -/
public noncomputable section
open Set Function Filter MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

set_option maxHeartbeats 1200000 in
theorem entropy_iterate_of_expansive (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (μ : ProbabilityMeasure X) (invariant : MeasurePreserving T (μ : Measure X) μ)
    (n : ℕ) (positive : 0 < n) :
    entropy ((T : X → X)^[n]) (μ : Measure X) =
      (((n : ℝ) * (entropy T (μ : Measure X)).toReal : ℝ) : EReal) := by
  obtain ⟨k, P, _, mesh⟩ := exists_small_boundary_partition (μ : Measure X) c positiveC
  have generator := P.entropy_eq_generator_rate T c expansive
    (fun i x y hx hy => (mesh i x y hx hy).le) μ invariant
  rw [generator, EReal.toReal_coe]
  apply le_antisymm
  · unfold entropy
    apply iSup_le
    intro l
    apply iSup_le
    intro Q
    rw [Q.liminf_eq_entropyRate _ (μ : Measure X) (invariant.iterate n)]
    apply EReal.coe_le_coe_iff.mpr
    apply (Q.entropyRate_iterate_le T (μ : Measure X) invariant n positive).trans
    exact mul_le_mul_of_nonneg_left
      (P.entropyRate_le_generator Q T c expansive
        (fun i x y hx hy => (mesh i x y hx hy).le) μ invariant) (Nat.cast_nonneg n)
  · unfold entropy
    apply le_iSup_of_le (Fintype.card (Fin n → Fin k))
    apply le_iSup_of_le (P.blockPartition T invariant.measurable n)
    rw [(P.blockPartition T invariant.measurable n).liminf_eq_entropyRate _
      (μ : Measure X) (invariant.iterate n), P.blockPartition_entropyRate T (μ : Measure X) invariant n positive]

end LeanShared.ThermodynamicDefinitions
