module

public import LeanShared.Dynamics.CompactPartitionCores

/-! Approximation of an arbitrary finite measurable partition by any
sufficiently fine finite partition, with an actual probability error bound. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Every finite measurable partition can be predicted, with arbitrarily
small error, from every sufficiently fine finite partition. -/
theorem MeasurablePartition.exists_prediction_scale {k : ℕ}
    (P : MeasurablePartition (X := X) k) (μ : ProbabilityMeasure X)
    (ε : ℝ) (positive : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, ∀ R : MeasurablePartition (X := X) r,
      (∀ i x y, x ∈ R.atom i → y ∈ R.atom i → dist x y < δ) →
      ∃ prediction : Fin r → Fin k,
        (μ : Measure X).real {x | P.label x ≠ prediction (R.label x)} < ε := by
  classical
  let : Nonempty X := nonempty_of_isProbabilityMeasure (μ : Measure X)
  obtain ⟨K,subset,compact,small⟩ := P.exists_compact_cores μ ε positive
  obtain ⟨δ,positiveδ,separated⟩ := P.compact_cores_separated K subset compact
  refine ⟨δ,positiveδ,?_⟩
  intro r R mesh
  let prediction : Fin r → Fin k := fun j =>
    if h : ∃ i, (K i ∩ R.atom j).Nonempty then Classical.choose h
    else P.label (Classical.arbitrary X)
  have correct (x : X) (hx : x ∈ ⋃ i, K i) : P.label x=prediction (R.label x) := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    have witness : ∃ l, (K l ∩ R.atom (R.label x)).Nonempty :=
      ⟨i,x,hi,R.label_mem x⟩
    have chosen : Classical.choose witness=i := by
      obtain ⟨y,hyK,hyR⟩ := Classical.choose_spec witness
      by_contra different
      exact (not_lt_of_ge (mesh _ y x hyR (R.label_mem x)).le)
        (separated _ _ different y hyK x hi)
    have label : P.label x=i := (P.label_eq_iff x i).mpr (subset i hi)
    dsimp only [prediction]
    rw [dite_eq_left witness,chosen,label]
  refine ⟨prediction,lt_of_le_of_lt (measureReal_mono ?_) small⟩
  intro x mismatch member
  exact mismatch (correct x member)

end LeanShared.ThermodynamicDefinitions
