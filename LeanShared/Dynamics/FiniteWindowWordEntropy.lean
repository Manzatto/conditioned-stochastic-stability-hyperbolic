module

public import LeanShared.Dynamics.ObservationPartitionEntropy
public import LeanShared.Dynamics.ExpansiveFinitePrediction
import all LeanShared.Dynamics.FiniteExpansiveWords

/-! A finite-window observation of a partition has word entropy bounded
by the original partition with only a fixed observation-horizon padding. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k l : ℕ}
namespace MeasurablePartition
open LeanShared.FiniteObservationEntropy

private def extractName (n N : ℕ)
    (prediction : ((Fin (N+1) → Fin k) × (Fin (N+1) → Fin k)) → Fin l)
    (w : Fin (n+2*N+1) → Fin k) : Fin n → Fin l := fun i => prediction
      (⟨fun j => w ⟨i.val+N+j.val,by omega⟩,
        fun j => w ⟨i.val+N-j.val,by omega⟩⟩)

omit [BorelSpace X] in
private theorem extractName_eq (P : MeasurablePartition (X := X) k) (T : X ≃ₜ X) (n N : ℕ)
    (prediction : ((Fin (N+1) → Fin k) × (Fin (N+1) → Fin k)) → Fin l) :
    (fun x (i : Fin n) => prediction (P.finiteName T N ((T : X → X)^[i.val] x))) =
      extractName n N prediction ∘ P.wordObservation T (n+2*N+1) ∘ (T.symm : X → X)^[N] := by
  funext x i
  apply congrArg prediction
  apply Prod.ext
  · funext j
    have equal := LeanShared.FiniteExpansiveWords.forward_rebase T j.val i.val N x
    rw [show j.val+i.val+N=i.val+N+j.val by omega] at equal
    exact congrArg P.label equal
  · funext j
    exact congrArg P.label (LeanShared.FiniteExpansiveWords.backward_rebase T j.val i.val N (by omega) x)

/-- The padding is fixed by the observation window and does not grow
with the entropy horizon n. -/
theorem finite_window_entropy_bound (P : MeasurablePartition (X := X) k) (T : X ≃ₜ X)
    (μ : Measure X) [IsFiniteMeasure μ] (invariant : MeasurePreserving T μ μ) (n N : ℕ)
    (prediction : ((Fin (N+1) → Fin k) × (Fin (N+1) → Fin k)) → Fin l) :
    LeanShared.FiniteObservationEntropy.entropy μ (fun x (i : Fin n) => prediction (P.finiteName T N ((T : X → X)^[i.val] x))) ≤
      dynamicalEntropy P T μ (n+2*N+1) := by
  have inverse : MeasurePreserving T.symm μ μ := MeasurePreserving.symm T.toMeasurableEquiv invariant
  have meas := P.wordObservation_measurable T T.continuous.measurable (n+2*N+1)
  have bound := entropy_comp_le μ
    (P.wordObservation T (n+2*N+1) ∘ (T.symm : X → X)^[N])
    (extractName n N prediction) (meas.comp (T.symm.continuous.measurable.iterate N))
  rw [←P.extractName_eq T n N prediction] at bound
  have same := entropy_comp_measurePreserving μ (T.symm : X → X)^[N] (inverse.iterate N)
    (P.wordObservation T (n+2*N+1)) meas
  rw [same,P.wordObservation_entropy T μ (n+2*N+1)] at bound
  exact bound

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
