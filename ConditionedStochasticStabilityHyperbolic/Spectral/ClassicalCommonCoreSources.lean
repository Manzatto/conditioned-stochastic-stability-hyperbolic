module

public import ConditionedStochasticStabilityHyperbolic.Spectral.UniformSameCutoffSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniApplication

/-! The cited same-operator common-core comparison has no dependence on KL
projectors or the chosen noisy leading eigenvalue. Its all-spectral-parameter
statement specializes to the produced KL branch internally. -/

@[expose] public noncomputable section
open scoped BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W Z Zret Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Exact classical Appendix-A comparison outside a common essential cutoff.
It compares the SAME cutoff operator on its two Banach realizations. -/
structure CommonCoreSpectralFacts
    (P : E →L[ℂ] E) (C : AbsorbingMarkovChains.CanonicalChain Y)
    (hC : HasStrongFellerKernel C) (R ρ : ℝ)
    (a : E →L[ℂ] Z) (b : (Y →ᵇ ℂ) →L[ℂ] Z) where
  ordinary : ComparedSpectralGap.EigenvectorComparison P
    ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC) a b ρ
  generalized : ∀ z : ℂ, ρ < ‖z‖ → GeneralizedSpectralComparison.Comparison P
    ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC) a b z
  reverse : CutoffEigenvectorLifting.ClassicalRealization P
    ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC) a b ρ

/-- The leading generalized comparison is selected using the proved KL
strict separation; it is not a source fact about an unknown noisy branch. -/
def ClassicalSameCutoffComparisons.ofCommonCoreFacts
    {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
    {d : DeterministicLeading (P 0)} {q δ : ℝ}
    (o : ProjectorOutputs P i d q δ) (hδlead : δ < d.rate - q) (hq : 0 < q)
    (ε : ℝ≥0) (hε : ε ≤ o.window) (c : RealOperatorConjugation (P ε))
    (C : AbsorbingMarkovChains.CanonicalChain Y) (hC : HasStrongFellerKernel C)
    (R : ℝ) (hR : 0 < R) (V : Set Y)
    (a : E →L[ℂ] Z) (b : (Y →ᵇ ℂ) →L[ℂ] Z)
    (restriction : Z →L[ℂ] Zret) (retained : (V →ᵇ ℂ) →L[ℂ] Zret)
    (hretained : Function.Injective retained)
    (hrestriction : restriction.comp b = retained.comp (Restriction.restrictObservable V))
    (facts : CommonCoreSpectralFacts ((R : ℂ) • P ε) C hC R (R * q) a b)
    (ultra : StrongFellerSquareCompact.UltraFellerContract (X := Y))
    (fredholm : PowerCompactGap.SquareCompactFredholm (F := Y →ᵇ ℂ))
    (riesz : PowerCompactRealLeadingPair.ClassicalContract (X := Y)) :
    ClassicalSameCutoffComparisons (Z := Z) (Zret := Zret) o ε C hC R V := by
  refine {
    parameterSmall := hε
    conjugation := c
    analyticAmbient := a
    physicalAmbient := b
    restriction := restriction
    retainedAmbient := retained
    retained_injective := hretained
    restriction_identity := hrestriction
    ordinary := facts.ordinary
    generalized := facts.generalized _ ?_
    reverse := facts.reverse
    ultraFeller := ultra
    fredholm := fredholm
    riesz := riesz }
  rw [Complex.norm_real, Real.norm_of_nonneg (mul_pos hR (hq.trans (o.eigenvalue_re_gt hδlead ε hε))).le]
  exact mul_lt_mul_of_pos_left (o.eigenvalue_re_gt hδlead ε hε) hR

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
