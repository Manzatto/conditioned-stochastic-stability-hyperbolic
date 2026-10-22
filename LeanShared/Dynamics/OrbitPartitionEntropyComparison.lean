module

public import LeanShared.Dynamics.UniformPredictionEntropy
public import LeanShared.Dynamics.CompactPartitionApproximation
public import LeanShared.Dynamics.PartitionMeasurableTransport
public import LeanShared.Dynamics.FiniteConditionalWordFixed
public import LeanShared.Dynamics.ConditionalDataProcessing

/-! Arbitrarily small entropy per iterate is lost when a finite orbit
partition is replaced by any sufficiently fine actual Bowen partition. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
namespace MeasurablePartition
open LeanShared.FiniteObservationEntropy

theorem exists_orbit_partition_entropy_bound (P : MeasurablePartition (X := X) k)
    (T : X ≃ₜ X) (μ : ProbabilityMeasure X)
    (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (η : ℝ) (positive : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ), 0 < n → ∀ (l : ℕ)
      (Q : MeasurablePartition (X := X) l),
      (∀ i x y, x ∈ Q.atom i → y ∈ Q.atom i → ∀ j < n,
        dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) < δ) →
      dynamicalEntropy P T (μ : Measure X) n ≤
        LeanShared.FiniteObservationEntropy.entropy (μ : Measure X) Q.label + (n : ℝ)*η := by
  classical
  obtain ⟨error,errorpositive,small⟩ := P.exists_conditional_error_bound (μ : Measure X) η positive
  obtain ⟨δ,δpositive,predict⟩ := P.exists_prediction_scale μ error errorpositive
  refine ⟨δ,δpositive,?_⟩
  intro n npositive l Q mesh
  have cancelF (j : ℕ) := Function.LeftInverse.iterate
    (f := (T.symm : X → X)) (g := (T : X → X)) (fun x => T.apply_symm_apply x) j
  have cancelB (j : ℕ) := Function.LeftInverse.iterate
    (f := (T : X → X)) (g := (T.symm : X → X)) (fun x => T.symm_apply_apply x) j
  have costs (j : Fin n) :
      conditional (μ : Measure X) (P.label ∘ (T : X → X)^[j.val]) Q.label ≤ η := by
    let Qj := Q.comap ((T.symm : X → X)^[j.val]) (T.symm.continuous.iterate j.val).measurable
    have meshj (i) (x y : X) (hx : x ∈ Qj.atom i) (hy : y ∈ Qj.atom i) : dist x y < δ := by
      have result := mesh i _ _ hx hy j.val j.isLt
      simpa only [cancelF j.val x,cancelF j.val y] using result
    obtain ⟨p,errorbound⟩ := predict l Qj meshj
    have mp : Measurable p := measurable_of_finite p
    have mg : Measurable (p ∘ Qj.label) := mp.comp Qj.label_measurable
    have cost := small (p ∘ Qj.label) mg errorbound
    have transport := conditional_comp_measurePreserving (μ : Measure X) (T : X → X)^[j.val]
      (invariant.iterate j.val) P.label (p ∘ Qj.label) P.label_measurable mg
    have equal : (p ∘ Qj.label) ∘ (T : X → X)^[j.val] = p ∘ Q.label := by
      funext x
      simp only [Function.comp_apply,Qj,comap_label]
      rw [cancelB j.val x]
    rw [equal] at transport
    have decrease := conditional_comp_le (μ : Measure X) (P.label ∘ (T : X → X)^[j.val])
      Q.label p (P.label_measurable.comp (T.continuous.iterate j.val).measurable)
      Q.label_measurable mp
    exact decrease.trans (transport.trans_le cost.le)
  have words := conditional_word_fixed_le (μ : Measure X) n npositive
    (fun j : Fin n => P.label ∘ (T : X → X)^[j.val]) Q.label
    (fun j => P.label_measurable.comp (T.continuous.iterate j.val).measurable) Q.label_measurable
  have summed : (∑ j : Fin n, conditional (μ : Measure X)
      (P.label ∘ (T : X → X)^[j.val]) Q.label) ≤ (n : ℝ)*η := by
    exact (Finset.sum_le_sum (fun j _ => costs j)).trans_eq (by simp)
  have lower := conditional_nonnegative (μ : Measure X) (P.wordObservation T n) Q.label
    (P.wordObservation_measurable T T.continuous.measurable n) Q.label_measurable
  have action : (fun x (j : Fin n) => (P.label ∘ (T : X → X)^[j.val]) x)=P.wordObservation T n := rfl
  rw [action] at words
  have bound := words.trans summed
  dsimp only [conditional] at lower bound
  rw [P.wordObservation_entropy T (μ : Measure X) n] at lower
  linarith

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
