module

public import LeanShared.Dynamics.OrbitWordBlockingEntropy
public import LeanShared.Dynamics.ObservationPartitionEntropy
public import LeanShared.Dynamics.FiniteMapPartition

/-! The actual finite partition by n-step orbit words, observed under T^n,
has exactly the entropy of the original partition over the full nk-step
orbit word. No entropy scaling or generating assumption is used. -/
public noncomputable section
open Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions.MeasurablePartition
variable {X : Type*} [MeasurableSpace X] {l : ℕ}

@[expose] def blockPartition (P : MeasurablePartition (X := X) l) (T : X → X)
    (measurable : Measurable T) (n : ℕ) :
    MeasurablePartition (X := X) (Fintype.card (Fin n → Fin l)) :=
  of_finite_map (P.wordObservation T n) (P.wordObservation_measurable T measurable n)

theorem blockPartition_dynamicalEntropy (P : MeasurablePartition (X := X) l)
    (T : X → X) (measurable : Measurable T) (μ : Measure X) (n k : ℕ) :
    dynamicalEntropy (P.blockPartition T measurable n) (T^[n]) μ k =
      dynamicalEntropy P T μ (k * n) := by
  let e := Fintype.equivFin (Fin n → Fin l)
  let encode : (Fin k → Fin n → Fin l) → (Fin k → Fin (Fintype.card (Fin n → Fin l))) :=
    fun w i => e (w i)
  have injective : Injective encode := by
    intro u v same
    funext i
    exact e.injective (congrFun same i)
  have same : (P.blockPartition T measurable n).wordObservation (T^[n]) k =
      encode ∘ (fun x (i : Fin k) (j : Fin n) => P.label (T^[j.val] ((T^[n])^[i.val] x))) := by
    funext x i
    change (of_finite_map _ _).label _ = _
    rw [of_finite_map_label]
    rfl
  rw [← wordObservation_entropy, same]
  rw [LeanShared.FiniteObservationEntropy.entropy_injective μ _ encode injective]
  rw [LeanShared.FiniteObservationEntropy.entropy_orbit_word_blocks]
  exact P.wordObservation_entropy T μ (k * n)

end LeanShared.ThermodynamicDefinitions.MeasurablePartition
