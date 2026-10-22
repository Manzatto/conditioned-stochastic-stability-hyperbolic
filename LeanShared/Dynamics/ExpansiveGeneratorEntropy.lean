module

public import LeanShared.Dynamics.ExpansiveConditionalApproximation
public import LeanShared.Dynamics.FiniteWindowEntropyComparison
public import LeanShared.Dynamics.PartitionObservationConditional

/-! The Kolmogorov–Sinai finite-generator theorem for actual compact
expansive dynamics, proved from finite prediction and entropy chain bounds. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
namespace MeasurablePartition

theorem entropyRate_le_generator {k l : ℕ} (P : MeasurablePartition (X := X) k)
    (Q : MeasurablePartition (X := X) l) (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (mesh : ∀ i x y, x ∈ P.atom i → y ∈ P.atom i → dist x y ≤ c)
    (μ : ProbabilityMeasure X) (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X)) :
    Q.entropyRate T (μ : Measure X) ≤ P.entropyRate T (μ : Measure X) := by
  obtain ⟨f,measurable,finite,numeric⟩ := P.exists_conditional_approximations T c expansive mesh Q μ
  have cost : Tendsto (fun n => LeanShared.FiniteObservationEntropy.conditional (μ : Measure X) Q.label (f n))
      atTop (𝓝 0) := numeric.congr' (Eventually.of_forall (fun n =>
        (Q.predictionJoint_conditional_eq (μ : Measure X) (f n) (measurable n)).symm))
  have bound (n : ℕ) : Q.entropyRate T (μ : Measure X) ≤ P.entropyRate T (μ : Measure X) +
      LeanShared.FiniteObservationEntropy.conditional (μ : Measure X) Q.label (f n) := by
    obtain ⟨N,prediction,equal⟩ := finite n
    have result := P.entropyRate_le_finite_prediction Q T (μ : Measure X) invariant N prediction
    rwa [←equal] at result
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (by simpa only [add_zero] using cost.const_add (P.entropyRate T (μ : Measure X)))
    (Eventually.of_forall bound)

/-- The actual full KS entropy equals the actual entropy rate of every
partition with mesh below an expansivity constant. The equality is a
conclusion, not a generator or variational source assumption. -/
theorem entropy_eq_generator_rate {k : ℕ} (P : MeasurablePartition (X := X) k)
    (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (mesh : ∀ i x y, x ∈ P.atom i → y ∈ P.atom i → dist x y ≤ c)
    (μ : ProbabilityMeasure X) (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X)) :
    entropy T (μ : Measure X)=(P.entropyRate T (μ : Measure X) : EReal) := by
  unfold entropy
  apply le_antisymm
  · apply iSup_le
    intro l
    apply iSup_le
    intro Q
    rw [Q.liminf_eq_entropyRate T (μ : Measure X) invariant]
    exact EReal.coe_le_coe_iff.mpr (P.entropyRate_le_generator Q T c expansive mesh μ invariant)
  · apply le_iSup_of_le k
    apply le_iSup_of_le P
    rw [P.liminf_eq_entropyRate T (μ : Measure X) invariant]

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
