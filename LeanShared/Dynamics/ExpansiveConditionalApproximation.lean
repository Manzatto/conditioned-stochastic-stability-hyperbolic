module

public import LeanShared.Dynamics.ExpansiveFinitePrediction
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

theorem exists_conditional_approximations {k l : ℕ} (P : MeasurablePartition (X := X) k)
    (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (mesh : ∀ i x y, x ∈ P.atom i → y ∈ P.atom i → dist x y ≤ c)
    (Q : MeasurablePartition (X := X) l) (μ : ProbabilityMeasure X) :
    ∃ f : ℕ → X → Fin l, (∀ n, Measurable (f n)) ∧
      (∀ n, ∃ N : ℕ, ∃ prediction : ((Fin (N+1) → Fin k) × (Fin (N+1) → Fin k)) → Fin l,
        f n=prediction ∘ P.finiteName T N) ∧
      Tendsto (fun n =>
        -(∑ i, ∑ j, Q.predictionJoint (μ : Measure X) (f n) i j*
          Real.log (Q.predictionJoint (μ : Measure X) (f n) i j)) +
        ∑ j, (∑ i, Q.predictionJoint (μ : Measure X) (f n) i j)*
          Real.log (∑ i, Q.predictionJoint (μ : Measure X) (f n) i j)) atTop (𝓝 0) := by
  have approximation (n : ℕ) := P.exists_finite_prediction T c expansive mesh Q μ
    (1/(n+1 : ℝ)) (by positivity)
  choose N prediction small using approximation
  let f : ℕ → X → Fin l := fun n => prediction n ∘ P.finiteName T (N n)
  have measurable (n : ℕ) : Measurable (f n) :=
    (measurable_of_countable (prediction n)).comp (P.finiteName_measurable T (N n))
  refine ⟨f,measurable,fun n => ⟨N n,prediction n,rfl⟩,?_⟩
  apply Q.prediction_conditionalEntropy_tendsto (μ : Measure X) f measurable
  exact squeeze_zero (fun _ => measureReal_nonneg) (fun n => (small n).le)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
