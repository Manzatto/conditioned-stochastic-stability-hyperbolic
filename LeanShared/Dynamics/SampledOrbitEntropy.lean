module

public import LeanShared.Dynamics.ObservationPartitionEntropy

/-! Sampling every n-th entry of an actual finite orbit word cannot
increase its Shannon entropy. This supplies the opposite inequality to
exact block coding in entropy scaling for iterates. -/
public noncomputable section
open Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions.MeasurablePartition
variable {X : Type*} [MeasurableSpace X] {l : ℕ}

theorem dynamicalEntropy_iterate_le (P : MeasurablePartition (X := X) l)
    (T : X → X) (measurable : Measurable T) (μ : Measure X) [IsFiniteMeasure μ]
    (n k : ℕ) (positive : 0 < n) :
    dynamicalEntropy P (T^[n]) μ k ≤ dynamicalEntropy P T μ (k * n) := by
  let sample : (Fin (k * n) → Fin l) → (Fin k → Fin l) :=
    fun w i => w ⟨n * i.val, by nlinarith [i.isLt]⟩
  have same : P.wordObservation (T^[n]) k = sample ∘ P.wordObservation T (k * n) := by
    funext x i
    dsimp [wordObservation, sample]
    rw [← Function.iterate_mul]
  rw [← P.wordObservation_entropy, same, ← P.wordObservation_entropy]
  exact LeanShared.FiniteObservationEntropy.entropy_comp_le μ _ sample
    (P.wordObservation_measurable T measurable (k * n))

end LeanShared.ThermodynamicDefinitions.MeasurablePartition
