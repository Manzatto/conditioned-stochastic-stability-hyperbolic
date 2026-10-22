module

public import LeanShared.Dynamics.PartitionPredictionEntropy
public import LeanShared.Dynamics.ObservationPartitionEntropy

/-! Exact identification of the actual prediction error entropy with
the finite-observation conditional entropy used in the chain comparison. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}
namespace MeasurablePartition

theorem label_fiber (P : MeasurablePartition (X := X) k) (i : Fin k) :
    P.label ⁻¹' {i}=P.atom i := by
  ext x
  exact P.label_eq_iff x i

theorem predictionJoint_conditional_eq (P : MeasurablePartition (X := X) k)
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → Fin k) (measurable : Measurable f) :
    LeanShared.FiniteObservationEntropy.conditional μ P.label f =
      -(∑ i, ∑ j, P.predictionJoint μ f i j*Real.log (P.predictionJoint μ f i j)) +
      ∑ j, (∑ i, P.predictionJoint μ f i j)*Real.log (∑ i, P.predictionJoint μ f i j) := by
  have col (j : Fin k) : ∑ i, P.predictionJoint μ f i j=μ.real (f ⁻¹' {j}) := by
    dsimp only [predictionJoint]
    simp_rw [inter_comm (P.atom _) (f ⁻¹' {j})]
    have h := LeanShared.FiniteObservationEntropy.marginal μ (f ⁻¹' {j})
      ((measurableSet_singleton j).preimage measurable) P.label P.label_measurable
    simpa only [P.label_fiber] using h
  unfold LeanShared.FiniteObservationEntropy.conditional
  rw [LeanShared.FiniteObservationEntropy.pair_entropy]
  simp only [P.label_fiber]
  simp_rw [col]
  simp only [LeanShared.FiniteObservationEntropy.entropy,predictionJoint,sub_neg_eq_add]

theorem prediction_conditional_tendsto (P : MeasurablePartition (X := X) k)
    (μ : Measure X) [IsFiniteMeasure μ] (f : ℕ → X → Fin k) (measurable : ∀ n, Measurable (f n))
    (error : Tendsto (fun n => μ.real {x | P.label x ≠ f n x}) atTop (𝓝 0)) :
    Tendsto (fun n => LeanShared.FiniteObservationEntropy.conditional μ P.label (f n)) atTop (𝓝 0) := by
  simpa only [P.predictionJoint_conditional_eq μ _ (measurable _)] using
    P.prediction_conditionalEntropy_tendsto μ f measurable error

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
