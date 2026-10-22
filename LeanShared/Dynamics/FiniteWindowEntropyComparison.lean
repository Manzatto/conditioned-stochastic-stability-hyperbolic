module

public import LeanShared.Dynamics.FiniteWindowWordEntropy
public import LeanShared.Dynamics.PaddedEntropyRate

/-! The entropy-rate comparison with a finite-window prediction of the
generator; all word costs and padding are proved from actual observations. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k l : ℕ}
namespace MeasurablePartition
open LeanShared.FiniteObservationEntropy

theorem entropyRate_le_finite_prediction (P : MeasurablePartition (X := X) k)
    (Q : MeasurablePartition (X := X) l) (T : X ≃ₜ X) (μ : Measure X)
    [IsProbabilityMeasure μ] (invariant : MeasurePreserving T μ μ) (N : ℕ)
    (prediction : ((Fin (N+1) → Fin k) × (Fin (N+1) → Fin k)) → Fin l) :
    Q.entropyRate T μ ≤ P.entropyRate T μ +
      conditional μ Q.label (prediction ∘ P.finiteName T N) := by
  let f : X → Fin l := prediction ∘ P.finiteName T N
  have mf : Measurable f := (measurable_of_countable prediction).comp (P.finiteName_measurable T N)
  have finite (n : ℕ) : dynamicalEntropy Q T μ n ≤ dynamicalEntropy P T μ (n+2*N+1) +
      (n : ℝ)*conditional μ Q.label f := by
    let word : X → (Fin n → Fin l) := fun x i => f ((T : X → X)^[i.val] x)
    have wordMeas : Measurable word := measurable_pi_iff.mpr (fun i => mf.comp (invariant.measurable.iterate i.val))
    have lower := conditional_nonnegative μ (Q.wordObservation T n) word
      (Q.wordObservation_measurable T invariant.measurable n) wordMeas
    have cost := conditional_orbit_words_le μ T invariant Q.label f Q.label_measurable mf n
    change conditional μ (Q.wordObservation T n) word ≤ _ at cost
    have predicted := P.finite_window_entropy_bound T μ invariant n N prediction
    change LeanShared.FiniteObservationEntropy.entropy μ word ≤ _ at predicted
    dsimp only [conditional] at lower cost
    rw [←Q.wordObservation_entropy T μ n]
    dsimp only [conditional]
    linarith
  have bound : ∀ᶠ n : ℕ in atTop, dynamicalEntropy Q T μ n / n ≤
      dynamicalEntropy P T μ (n+(2*N+1)) / n + conditional μ Q.label f := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have positive : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      _ ≤ (dynamicalEntropy P T μ (n+2*N+1)+(n : ℝ)*conditional μ Q.label f)/n :=
        div_le_div_of_nonneg_right (finite n) positive.le
      _ = _ := by rw [Nat.add_assoc]; field_simp
  exact le_of_tendsto_of_tendsto (Q.entropyRate_tendsto T μ invariant)
    ((P.padded_entropyRate_tendsto T μ invariant (2*N+1)).add_const (conditional μ Q.label f)) bound

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
