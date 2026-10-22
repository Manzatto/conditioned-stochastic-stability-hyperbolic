module

public import ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
public import ConditionedStochasticStabilityHyperbolic.Spectral.LeadingSimplicity

/-! The literal theorem's eigenmeasure and product clauses follow from the
proved real rank-one gap. No separately supplied left eigenmeasure,
normalization, positivity or spectral-radius equation is needed. -/

@[expose] public noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (R : ℝ)
  (sf : HasStrongFellerKernel C)
  (d : RankOneSpectralData (R • strongFellerTransferOperator C sf) (1 : X →ᵇ ℝ))
  (positive : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) →
    ∀ x, 0 ≤ (R • strongFellerTransferOperator C sf) f x)

/-- All spectral clauses in the published statement are constructed from
the actual positive operator gap. -/
def SpectralWitness.of_rankOne (ν : ProbabilityMeasure X)
    (product : (ν : Measure X) = eigenvectorMeasure (d.eigenmeasure positive) d.eigenvector) :
    SpectralWitness C R ν where
  strongFeller := sf
  eigenfunction := d.eigenvector
  eigenfunction_nonnegative := d.eigenvector_nonneg_of_positive positive
  eigenmeasure := d.eigenmeasure positive
  finite_eigenmeasure := inferInstance
  rate := d.rate
  rate_positive := d.rate_pos
  right := d.right_eigenvector
  left := by
    intro f
    rw [← d.eigenmeasure_represents positive, ← d.eigenmeasure_represents positive]
    exact d.left_eigenfunctional f
  normalization := by
    rw [← d.eigenmeasure_represents positive]
    exact d.mean_eigenvector
  product := product
  radius := d.spectralRadius_eq_rate

/-- The pointwise theorem target can therefore use the rank-one datum
already returned by the spectral/support development. -/
theorem point_of_rankOne (ν : ProbabilityMeasure X) (core : Set X)
    (product : (ν : Measure X) = eigenvectorMeasure (d.eigenmeasure positive) d.eigenvector)
    (qem : C.IsQuasiErgodic (ν : Measure X)) (support : core ⊆ (ν : Measure X).support)
    (unique : ∀ ζ : Measure X, C.IsQuasiErgodic ζ → core ⊆ ζ.support → ζ = (ν : Measure X)) :
    Point C R core ν :=
  ⟨qem, support, unique, ⟨SpectralWitness.of_rankOne C R sf d positive ν product⟩⟩

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
