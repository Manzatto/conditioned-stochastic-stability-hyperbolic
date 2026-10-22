module
public import ConditionedStochasticStabilityHyperbolic.Paper.SimpleSpectralWitness
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapFamilyWindow
public import ConditionedStochasticStabilityHyperbolic.Spectral.Normalization

/-! Exact same-probability spectral witnesses, including both uniqueness
clauses, for an arbitrary positive raw normalization. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {C : AbsorbingMarkovChains.CanonicalChain X} {core : Set X}
  {ν : ProbabilityMeasure X}

/-- Retaining the normalized gap retains all raw leading spectral clauses
for exactly the same QEM probability. -/
theorem NormalizedGap.simpleWitness (gap : NormalizedGap C core ν)
    (R : ℝ) (hR : 0 < R) : Nonempty (SimpleSpectralWitness C R ν) := by
  obtain ⟨sf, d, hproduct, _hcore⟩ := gap
  have positive (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : X) :
      0 ≤ strongFellerTransferOperator C sf f x := by
    rw [strongFellerTransferOperator_represents]
    exact integral_nonneg hf
  let raw := d.rescale R hR
  have rawPositive (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : X) :
      0 ≤ (R • strongFellerTransferOperator C sf) f x := by
    change 0 ≤ R * strongFellerTransferOperator C sf f x
    exact mul_nonneg hR.le (positive f hf x)
  have measures : raw.eigenmeasure rawPositive = d.eigenmeasure positive := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [← raw.eigenmeasure_represents rawPositive, ← d.eigenmeasure_represents positive]
    rfl
  refine ⟨SimpleSpectralWitness.of_rankOne C R sf raw rawPositive ν ?_⟩
  rw [measures]
  exact hproduct

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
