module
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalSpectralWitness
import all ConditionedStochasticStabilityHyperbolic.Paper.LocalSpectralWitness
public import ConditionedStochasticStabilityHyperbolic.Spectral.LeadingEigenmeasure

/-! The full leading eigenfunction and eigenmeasure uniqueness clauses are
retained explicitly, in addition to the radius and probability product. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

structure SimpleSpectralWitness (C : AbsorbingMarkovChains.CanonicalChain X)
    (R : ℝ) (ν : ProbabilityMeasure X) extends SpectralWitness C R ν where
  right_unique : ∀ f : X →ᵇ ℝ,
    (R • strongFellerTransferOperator C strongFeller) f = rate • f →
      ∃ c : ℝ, f = c • eigenfunction
  left_unique : ∀ (μ : Measure X) [IsFiniteMeasure μ],
    (∀ f : X →ᵇ ℝ,
      (∫ x, ((R • strongFellerTransferOperator C strongFeller) f) x ∂μ) =
        rate * ∫ x, f x ∂μ) →
    μ = ENNReal.ofReal (∫ x, eigenfunction x ∂μ) • eigenmeasure

variable (C : AbsorbingMarkovChains.CanonicalChain X) (R : ℝ)
  (sf : HasStrongFellerKernel C)
  (d : RankOneSpectralData (R • strongFellerTransferOperator C sf) (1 : X →ᵇ ℝ))
  (positive : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) →
    ∀ x, 0 ≤ (R • strongFellerTransferOperator C sf) f x)

/-- The actual positive power gap supplies both simplicity clauses. -/
def SimpleSpectralWitness.of_rankOne (ν : ProbabilityMeasure X)
    (product : (ν : Measure X) = eigenvectorMeasure (d.eigenmeasure positive) d.eigenvector) :
    SimpleSpectralWitness C R ν where
  toSpectralWitness := SpectralWitness.of_rankOne C R sf d positive ν product
  right_unique := fun f hf => ⟨d.mean f, d.leading_eigenvector_eq f hf⟩
  left_unique := by
    intro μ hμ hleft
    change (∀ f : X →ᵇ ℝ,
      (∫ x, ((R • strongFellerTransferOperator C sf) f) x ∂μ) =
        d.rate * ∫ x, f x ∂μ) at hleft
    change μ = ENNReal.ofReal (∫ x, d.eigenvector x ∂μ) • d.eigenmeasure positive
    let ℓ := AbsorbingMarkovChains.LeftSimplicity.integralFunctional μ
    have hℓ (f : X →ᵇ ℝ) : ℓ f = ∫ x, f x ∂μ :=
      AbsorbingMarkovChains.LeftSimplicity.integralFunctional_apply μ f
    have he := d.leading_eigenfunctional_eq ℓ (by
      intro f
      simpa only [hℓ] using hleft f)
    have hc : 0 ≤ ℓ d.eigenvector :=
      integral_nonneg (d.eigenvector_nonneg_of_positive positive)
    let _ : IsFiniteMeasure
        (ENNReal.ofReal (∫ x, d.eigenvector x ∂μ) • d.eigenmeasure positive) :=
      (d.eigenmeasure positive).smul_finite ENNReal.ofReal_ne_top
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    have hf := congrArg (fun q : (X →ᵇ ℝ) →L[ℝ] ℝ => q f) he
    change (∫ x, f x ∂μ) = _
    rw [integral_smul_measure, ← hℓ d.eigenvector, ENNReal.toReal_ofReal hc,
      smul_eq_mul, ← d.eigenmeasure_represents positive f]
    simpa only [smul_apply, smul_eq_mul, hℓ f] using hf

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
