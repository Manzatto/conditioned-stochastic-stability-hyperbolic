module

public import LeanShared.Dynamics.BlockGeneratorPrediction
public import LeanShared.Dynamics.PartitionPredictionEntropy
public import Mathlib.Analysis.SpecificLimits.Basic

/-! A compact expansive generator approximates every finite measurable
partition with conditional entropy tending to zero. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
namespace MeasurablePartition

theorem exists_block_conditional_approximations {k l : ℕ} (P : MeasurablePartition (X := X) k)
    (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (n : ℕ) (positiveN : 0 < n)
    (mesh : ∀ i x y, x ∈ P.atom i → y ∈ P.atom i →
      ∀ j < n, dist (T^[j] x) (T^[j] y) ≤ c)
    (Q : MeasurablePartition (X := X) l) (μ : ProbabilityMeasure X) :
    ∃ f : ℕ → X → Fin l, (∀ n, Measurable (f n)) ∧
      (∀ m, ∃ N : ℕ, ∃ prediction : ((Fin (N+1) → Fin k) × (Fin (N+1) → Fin k)) → Fin l,
        f m=prediction ∘ P.finiteName (T^n) N) ∧
      Tendsto (fun n =>
        -(∑ i, ∑ j, Q.predictionJoint (μ : Measure X) (f n) i j*
          Real.log (Q.predictionJoint (μ : Measure X) (f n) i j)) +
        ∑ j, (∑ i, Q.predictionJoint (μ : Measure X) (f n) i j)*
          Real.log (∑ i, Q.predictionJoint (μ : Measure X) (f n) i j)) atTop (𝓝 0) := by
  have approximation (m : ℕ) := P.exists_block_finite_prediction T c expansive n positiveN mesh Q μ
    (1/(m+1 : ℝ)) (by positivity)
  choose N prediction small using approximation
  let f : ℕ → X → Fin l := fun m => prediction m ∘ P.finiteName (T^n) (N m)
  have measurable (m : ℕ) : Measurable (f m) :=
    (measurable_of_countable (prediction m)).comp (P.finiteName_measurable (T^n) (N m))
  refine ⟨f,measurable,fun n => ⟨N n,prediction n,rfl⟩,?_⟩
  apply Q.prediction_conditionalEntropy_tendsto (μ : Measure X) f measurable
  exact squeeze_zero (fun _ => measureReal_nonneg) (fun n => (small n).le)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
