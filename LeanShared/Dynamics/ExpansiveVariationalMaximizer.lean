module

public import LeanShared.Dynamics.ExpansiveEntropyUpperSemicontinuity
public import LeanShared.Dynamics.CompactInvariantMeasures

/-! Attainment of the actual entropy-plus-potential functional on compact
expansive systems. Its identification with separated pressure is separate. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem entropy_finite_of_expansive (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (μ : ProbabilityMeasure X) (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X)) :
    ∃ H : ℝ, entropy T (μ : Measure X)=(H : EReal) := by
  obtain ⟨k,P,_,mesh,_,_⟩ := exists_expansive_null_boundary_generator T c positive expansive (μ : Measure X)
  exact ⟨P.entropyRate T (μ : Measure X), P.entropy_eq_generator_rate T c expansive
    (fun i x y hx hy => (mesh i x y hx hy).le) μ invariant⟩

/-- An actual invariant entropy-plus-energy maximizing probability is
constructed from compactness and proved full-entropy upper semicontinuity. -/
theorem exists_entropy_variational_maximizer [Nonempty X]
    (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (φ : X → ℝ) (continuous : Continuous φ) :
    ∃ μ : ProbabilityMeasure X, MeasurePreserving T (μ : Measure X) (μ : Measure X) ∧
      (∃ H : ℝ, entropy T (μ : Measure X)=(H : EReal)) ∧
      ∀ ν : ProbabilityMeasure X, MeasurePreserving T (ν : Measure X) (ν : Measure X) →
        (entropy T (ν : Measure X)).toReal + (∫ x, φ x ∂(ν : Measure X)) ≤
          (entropy T (μ : Measure X)).toReal + (∫ x, φ x ∂(μ : Measure X)) := by
  let f : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨φ,continuous⟩
  have entropyUSC := entropy_toReal_upperSemicontinuousOn_invariant T c positive expansive
  have integralContinuous := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
  have objective : UpperSemicontinuousOn
      (fun μ : ProbabilityMeasure X => (entropy T (μ : Measure X)).toReal + ∫ x, φ x ∂(μ : Measure X))
      {μ | MeasurePreserving T (μ : Measure X) (μ : Measure X)} := by
    intro μ invariant
    exact UpperSemicontinuousWithinAt.add (entropyUSC μ invariant)
      (integralContinuous.continuousAt.upperSemicontinuousAt.upperSemicontinuousWithinAt _)
  obtain ⟨μ,invariant,maximal⟩ := objective.exists_isMaxOn
    (LeanShared.EmpiricalProbability.compact_nonempty_invariant T T.continuous).2
    (LeanShared.EmpiricalProbability.compact_nonempty_invariant T T.continuous).1
  exact ⟨μ,invariant,entropy_finite_of_expansive T c positive expansive μ invariant,maximal⟩

end LeanShared.ThermodynamicDefinitions
