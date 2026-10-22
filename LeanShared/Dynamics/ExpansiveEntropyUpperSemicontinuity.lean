module

public import LeanShared.Dynamics.ExpansiveGeneratorEntropy
public import LeanShared.Dynamics.ExpansiveNullBoundaryGenerator

/-! Upper semicontinuity of the actual full Kolmogorov–Sinai entropy
on the invariant probabilities of a compact expansive system. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- This is the full entropy, not a fixed-partition surrogate. Null-boundary
finite generators are constructed separately at each limiting law. -/
theorem entropy_upperSemicontinuousOn_invariant (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y) :
    UpperSemicontinuousOn (fun μ : ProbabilityMeasure X => entropy T (μ : Measure X))
      {μ | MeasurePreserving T (μ : Measure X) (μ : Measure X)} := by
  intro μ invariant
  obtain ⟨k,P,boundary,mesh,_,_⟩ := exists_expansive_null_boundary_generator T c positive expansive (μ : Measure X)
  have mesh' := fun i x y hx hy => (mesh i x y hx hy).le
  have rate := P.entropyRate_upperSemicontinuousAt T T.continuous μ invariant boundary
  have coe := continuous_coe_real_ereal.continuousAt.comp_upperSemicontinuousAt rate
    (fun x y hxy => EReal.coe_le_coe_iff.mpr hxy)
  have source : UpperSemicontinuousAt
      (fun ν : ProbabilityMeasure X => (P.entropyRate T (ν : Measure X) : EReal)) μ := coe
  apply (source.upperSemicontinuousWithinAt _).congr_of_eventuallyEq invariant
  filter_upwards [self_mem_nhdsWithin] with ν hν
  exact (P.entropy_eq_generator_rate T c expansive mesh' ν hν).symm

/-- The full entropy is finite and its actual real value is also upper
semicontinuous on invariant probabilities. -/
theorem entropy_toReal_upperSemicontinuousOn_invariant (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y) :
    UpperSemicontinuousOn (fun μ : ProbabilityMeasure X => (entropy T (μ : Measure X)).toReal)
      {μ | MeasurePreserving T (μ : Measure X) (μ : Measure X)} := by
  intro μ invariant
  obtain ⟨k,P,boundary,mesh,_,_⟩ := exists_expansive_null_boundary_generator T c positive expansive (μ : Measure X)
  have mesh' := fun i x y hx hy => (mesh i x y hx hy).le
  have source := P.entropyRate_upperSemicontinuousAt T T.continuous μ invariant boundary
  apply (source.upperSemicontinuousWithinAt _).congr_of_eventuallyEq invariant
  filter_upwards [self_mem_nhdsWithin] with ν hν
  rw [P.entropy_eq_generator_rate T c expansive mesh' ν hν,EReal.toReal_coe]

end LeanShared.ThermodynamicDefinitions
