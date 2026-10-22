module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CommonCoreSeed
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexPowerConvergence
public import ConditionedStochasticStabilityHyperbolic.Spectral.RegularCoreApproximation

/-! # Physical integration from invariant finite-regular core powers

The source packet has no regular noisy-eigenvector witness, no C0-to-Cu
smoothing assumption, no product integral identity, and no physical complex
gap. Core invariance, exact projector compatibility and produced analytic and
real gaps construct simultaneous product approximants internally.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.InvariantPhysicalPairing
open Restriction

variable {H Z Core X : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Exact physical and cited same-cutoff invariant-core source data. The
core is the finite-regular supported common core (or its little completion),
not a claim that noisy eigenfunctions are smooth. -/
structure Inputs (Pa Anorm : H →L[ℂ] H) (γ : H) (ν : ProbabilityMeasure X)
    (A : Set (X →ᵇ ℝ)) (M : A → H →L[ℂ] H) where
  original : AbsorbingMarkovChains.CanonicalChain X
  cutoff : AbsorbingMarkovChains.CanonicalChain X
  originalSF : HasStrongFellerKernel original
  cutoffSF : HasStrongFellerKernel cutoff
  retained : Set X
  badOriginal : Set X
  badCutoff : Set X
  retainedMeasurable : MeasurableSet retained
  noReturnOriginal : ∀ x : retained, ∀ᵐ y ∂original.killedTransition x.val,
    y ∉ retained → y ∈ badOriginal
  extinctOriginal : ∀ x ∈ badOriginal, ∃ n : ℕ,
    original.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0
  noReturnCutoff : ∀ x : retained, ∀ᵐ y ∂cutoff.killedTransition x.val,
    y ∉ retained → y ∈ badCutoff
  extinctCutoff : ∀ x ∈ badCutoff, ∃ n : ℕ,
    cutoff.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0
  retainedKernelEq : LeanShared.SubtypeKernel.restrict original.killedTransition
    retained retainedMeasurable = LeanShared.SubtypeKernel.restrict cutoff.killedTransition
    retained retainedMeasurable
  originalData : RankOneSpectralData
    (ComplexStrongFeller.transferOperator (𝕜 := ℝ) original originalSF) (1 : X →ᵇ ℝ)
  cutoffData : RankOneSpectralData
    (ComplexStrongFeller.transferOperator (𝕜 := ℝ) cutoff cutoffSF) (1 : X →ᵇ ℝ)
  rates : originalData.rate = cutoffData.rate
  retainedScalar : ℝ
  retainedScalar_ne : retainedScalar ≠ 0
  retainedVectors : restrictObservable retained originalData.eigenvector =
    retainedScalar • restrictObservable retained cutoffData.eigenvector
  retainedVector_ne : restrictObservable retained cutoffData.eigenvector ≠ 0
  originalLeftMeasure : Measure X
  originalLeftRep : ∀ f : X →ᵇ ℝ, originalData.mean f = ∫ x, f x ∂originalLeftMeasure
  probabilityProduct : (ν : Measure X) =
    LeanShared.eigenvectorMeasure originalLeftMeasure originalData.eigenvector
  cutoffLeftMeasure : Measure X
  cutoffLeft_finite : IsFiniteMeasure cutoffLeftMeasure
  cutoffLeftRep : ∀ f : X →ᵇ ℝ, cutoffData.mean f = ∫ x, f x ∂cutoffLeftMeasure
  analyticAmbient : H →L[ℂ] Z
  physicalAmbient : (X →ᵇ ℂ) →L[ℂ] Z
  regularity : ℝ
  positiveExponent : ℝ
  negativeExponent : ℝ
  regularOrder : ℝ
  margins : RegularCoreApproximation.RegularityMargins regularity positiveExponent
    negativeExponent regularOrder
  analyticCore : Core →L[ℂ] H
  physicalCore : Core →L[ℂ] (X →ᵇ ℂ)
  analyticCore_dense : DenseRange analyticCore
  normalizedCore : Core →L[ℂ] Core
  analyticCore_action : analyticCore.comp normalizedCore = Anorm.comp analyticCore
  physicalCore_action : physicalCore.comp normalizedCore =
    (((cutoffData.rate : ℂ)⁻¹ • ComplexStrongFeller.transferOperator (𝕜 := ℂ) cutoff cutoffSF)).comp
      physicalCore
  projectorCore : ∀ u : Core,
    letI := cutoffLeft_finite
    physicalAmbient ((ComplexLeadingMeasure.integralFunctional cutoffLeftMeasure).smulRight
      (AbsorbingMarkovChains.ComplexKernel.ofReal cutoffData.eigenvector) (physicalCore u)) =
    analyticAmbient (Pa (analyticCore u))
  analyticScalar : ℂ
  analyticScalar_ne : analyticScalar ≠ 0
  ambientVectors : physicalAmbient
    (AbsorbingMarkovChains.ComplexKernel.ofReal cutoffData.eigenvector) =
    analyticScalar • analyticAmbient γ
  analyticVector_ne : analyticAmbient γ ≠ 0
  coreMultiplier : A → Core →L[ℂ] Core
  multiplier_physical : ∀ h : A, ∀ u : Core,
    physicalCore (coreMultiplier h u) = physicalCore u *
      AbsorbingMarkovChains.ComplexKernel.ofReal h.val
  multiplier_analytic : ∀ h : A, analyticCore.comp (coreMultiplier h) =
    (M h).comp analyticCore

/-- The analytic operator power limit and actual real physical gap construct
observable product pairings through one invariant common-core seed. -/
theorem Inputs.integral_eq
    {Pa Anorm : H →L[ℂ] H} {γ : H} {ν : ProbabilityMeasure X}
    {A : Set (X →ᵇ ℝ)} {M : A → H →L[ℂ] H}
    (I : Inputs (Z := Z) (Core := Core) Pa Anorm γ ν A M)
    (ma : H →L[ℂ] ℂ) (hPa : Pa = ma.smulRight γ) (hnorm : ma γ = 1)
    (hpower : Tendsto (fun n : ℕ => Anorm ^ n) atTop (𝓝 Pa)) (h : A) :
    (∫ x, h.val x ∂(ν : Measure X)) = (ma (M h γ)).re := by
  let _ := I.cutoffLeft_finite
  let ℓ := ComplexLeadingMeasure.integralFunctional I.cutoffLeftMeasure
  let Pp := ℓ.smulRight (AbsorbingMarkovChains.ComplexKernel.ofReal I.cutoffData.eigenvector)
  obtain ⟨seed, hseedP, hseedA⟩ := CommonCoreSeed.exists_normalized_seed
    I.analyticCore I.physicalCore I.analyticCore_dense Pa Pp ma ℓ γ
    (AbsorbingMarkovChains.ComplexKernel.ofReal I.cutoffData.eigenvector) hPa rfl hnorm
    I.analyticAmbient I.physicalAmbient I.projectorCore I.analyticScalar I.ambientVectors
    I.analyticVector_ne
  have hlimA : Tendsto (fun n : ℕ => (Anorm ^ n) (I.analyticCore seed)) atTop
      (𝓝 (I.analyticScalar • γ)) := by
    have ht := (ContinuousLinearMap.apply ℂ H (I.analyticCore seed)).continuous.continuousAt.tendsto.comp hpower
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, hseedA] using ht
  have hcomm (f : X →ᵇ ℝ) :
      ComplexStrongFeller.transferOperator (𝕜 := ℂ) I.cutoff I.cutoffSF
        (AbsorbingMarkovChains.ComplexKernel.ofReal f) =
      AbsorbingMarkovChains.ComplexKernel.ofReal
        (ComplexStrongFeller.transferOperator (𝕜 := ℝ) I.cutoff I.cutoffSF f) := by
    rw [CanonicalChainGap.realTransfer_eq]
    exact NoiseSpectralGap.complexTransfer_ofReal _ _ f
  have hlimP := ComplexPowerConvergence.tendsto_normalized_apply_of_intertwining
    (ComplexStrongFeller.transferOperator (𝕜 := ℝ) I.cutoff I.cutoffSF)
    (ComplexStrongFeller.transferOperator (𝕜 := ℂ) I.cutoff I.cutoffSF) hcomm I.cutoffData
    I.cutoffLeftMeasure I.cutoffLeftRep (I.physicalCore seed)
  change Tendsto _ atTop (𝓝 (Pp (I.physicalCore seed))) at hlimP
  rw [hseedP] at hlimP
  obtain ⟨u, hup, hua⟩ := InvariantCoreProductApproximation.exists_product_approximants_of_invariant_core
    I.normalizedCore Anorm
    ((I.cutoffData.rate : ℂ)⁻¹ • ComplexStrongFeller.transferOperator (𝕜 := ℂ) I.cutoff I.cutoffSF)
    I.analyticCore I.physicalCore I.analyticCore_action I.physicalCore_action
    1 seed γ I.cutoffData.eigenvector I.analyticScalar
    (by simpa only [inv_one, one_smul] using hlimA)
    (by simpa only [inv_one, one_smul] using hlimP)
    (I.coreMultiplier h) (M h) h.val (I.multiplier_analytic h) (I.multiplier_physical h)
  rw [I.probabilityProduct]
  exact PhysicalProjectorPairing.integral_eq_analytic_product
    I.original I.cutoff I.originalSF I.cutoffSF I.retained I.badOriginal I.badCutoff
    I.retainedMeasurable I.noReturnOriginal I.extinctOriginal I.noReturnCutoff
    I.extinctCutoff I.retainedKernelEq I.originalData I.cutoffData I.rates
    I.retainedScalar I.retainedScalar_ne I.retainedVectors I.retainedVector_ne
    I.originalLeftMeasure I.originalLeftRep ℓ
    (ComplexLeadingMeasure.integralFunctional_ofReal I.cutoffData I.cutoffLeftMeasure I.cutoffLeftRep)
    Pa Pp γ ma hPa rfl I.analyticAmbient I.physicalAmbient I.analyticCore I.physicalCore
    I.projectorCore I.analyticScalar I.analyticScalar_ne I.ambientVectors I.analyticVector_ne
    h.val ((M h).restrictScalars ℝ) u hup hua

end ConditionedStochasticStabilityHyperbolic.InvariantPhysicalPairing
