module

public import ConditionedStochasticStabilityHyperbolic.Spectral.InvariantPhysicalPairing
public import ConditionedStochasticStabilityHyperbolic.Spectral.RetainedCanonicalVectors
public import ConditionedStochasticStabilityHyperbolic.Spectral.CommonCoreTrace

/-! Constructed physical pairing packets. Produced original/cutoff gaps and
actual retained geometry determine the retained and ambient vector scalars.
The source common core supplies only invariant actions, literal multipliers
and same-cutoff Riesz-projector comparison, not product integrals or limits. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedInvariantPairing
open LeanShared Restriction

variable {H Z Core X : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

structure CoreSources (Pa Anorm : H →L[ℂ] H)
    (D : AbsorbingMarkovChains.CanonicalChain X) (hD : HasStrongFellerKernel D)
    (dc : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) D hD)
      (1 : X →ᵇ ℝ)) (μcut : Measure X) [IsFiniteMeasure μcut]
    (A : Set (X →ᵇ ℝ)) (M : A → H →L[ℂ] H) where
  analyticAmbient : H →L[ℂ] Z
  physicalAmbient : (X →ᵇ ℂ) →L[ℂ] Z
  supportedRegion : Set X
  regularity : ℝ
  positiveExponent : ℝ
  negativeExponent : ℝ
  regularOrder : ℝ
  margins : RegularCoreApproximation.RegularityMargins regularity positiveExponent
    negativeExponent regularOrder
  analyticCore : Core →L[ℂ] H
  physicalCore : Core →L[ℂ] (X →ᵇ ℂ)
  supportedCoreDensity : ∀ f : X →ᵇ ℂ, tsupport f ⊆ supportedRegion →
    f ∈ closure (range physicalCore)
  supportedFaithful : ∀ f : X →ᵇ ℂ, tsupport f ⊆ supportedRegion →
    physicalAmbient f = 0 → f = 0
  analyticCore_dense : DenseRange analyticCore
  normalizedCore : Core →L[ℂ] Core
  analyticCore_action : analyticCore.comp normalizedCore = Anorm.comp analyticCore
  physicalCore_action : physicalCore.comp normalizedCore =
    (((dc.rate : ℂ)⁻¹ • ComplexStrongFeller.transferOperator (𝕜 := ℂ) D hD)).comp
      physicalCore
  projectorCore : ∀ u : Core,
    physicalAmbient ((ComplexLeadingMeasure.integralFunctional μcut).smulRight
      (AbsorbingMarkovChains.ComplexKernel.ofReal dc.eigenvector) (physicalCore u)) =
    analyticAmbient (Pa (analyticCore u))
  coreMultiplier : A → Core →L[ℂ] Core
  multiplier_physical : ∀ h : A, ∀ u : Core,
    physicalCore (coreMultiplier h u) = physicalCore u *
      AbsorbingMarkovChains.ComplexKernel.ofReal h.val
  multiplier_analytic : ∀ h : A, analyticCore.comp (coreMultiplier h) =
    (M h).comp analyticCore

theorem exists_inputs_of_actual_gaps_and_core
    (C D : AbsorbingMarkovChains.CanonicalChain X)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D)
    (V BC BD : Set X) (hV : MeasurableSet V)
    (heq : SubtypeKernel.restrict C.killedTransition V hV =
      SubtypeKernel.restrict D.killedTransition V hV)
    (hreturnC : ∀ x : V, ∀ᵐ y ∂C.killedTransition x.val, y ∉ V → y ∈ BC)
    (hextC : ∀ x ∈ BC, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (hreturnD : ∀ x : V, ∀ᵐ y ∂D.killedTransition x.val, y ∉ V → y ∈ BD)
    (hextD : ∀ x ∈ BD, ∃ n : ℕ,
      D.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (NC ND : ℕ)
    (hcompC : ∀ x : ↥(Vᶜ), ((SubtypeKernel.restrict C.killedTransition Vᶜ hV.compl)^NC) x univ = 0)
    (hcompD : ∀ x : ↥(Vᶜ), ((SubtypeKernel.restrict D.killedTransition Vᶜ hV.compl)^ND) x univ = 0)
    (dor : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hC) (1 : X →ᵇ ℝ))
    (dc : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) D hD) (1 : X →ᵇ ℝ))
    (hrate : dor.rate = dc.rate) (μoriginal μcut : Measure X) [IsFiniteMeasure μcut]
    (hμoriginal : ∀ f : X →ᵇ ℝ, dor.mean f = ∫ x, f x ∂μoriginal)
    (hμcut : ∀ f : X →ᵇ ℝ, dc.mean f = ∫ x, f x ∂μcut)
    (ν : ProbabilityMeasure X) (hν : (ν : Measure X) = eigenvectorMeasure μoriginal dor.eigenvector)
    (Pa Anorm : H →L[ℂ] H) (γ : H) (ma : H →L[ℂ] ℂ) (hPa : Pa = ma.smulRight γ)
    (A : Set (X →ᵇ ℝ)) (M : A → H →L[ℂ] H)
    (s : CoreSources (Z := Z) (Core := Core) Pa Anorm D hD dc μcut A M)
    (hcutoffSupport : tsupport
      (AbsorbingMarkovChains.ComplexKernel.ofReal dc.eigenvector) ⊆ s.supportedRegion) :
    Nonempty (InvariantPhysicalPairing.Inputs (Z := Z) (Core := Core) Pa Anorm γ ν A M) := by
  obtain ⟨hretne, c, hc, hret⟩ := RetainedCanonicalVectors.exists_retained_scalar
    C D hC hD V BC BD hV heq hreturnC hextC hreturnD hextD NC ND hcompC hcompD dor dc hrate
  let ℓ := ComplexLeadingMeasure.integralFunctional μcut
  let gc := AbsorbingMarkovChains.ComplexKernel.ofReal dc.eigenvector
  let Pp := ℓ.smulRight gc
  have hnorm : ℓ gc = 1 := by
    rw [ComplexLeadingMeasure.integralFunctional_ofReal dc μcut hμcut, dc.mean_eigenvector]
    rfl
  have hg : s.physicalAmbient gc ≠ 0 := by
    intro hz
    have hh := s.supportedFaithful gc hcutoffSupport hz
    have he := congrArg ℓ hh
    rw [hnorm, map_zero] at he
    exact one_ne_zero he
  have htrace := CommonCoreSeed.exists_nonzero_core_trace_of_closure s.physicalCore ℓ gc
    (s.supportedCoreDensity gc hcutoffSupport) (by rw [hnorm]; exact one_ne_zero)
  obtain ⟨a, ha, hmatch, hane⟩ := CommonCoreSeed.exists_ambient_scalar_of_nonzero_core_trace
    s.analyticCore s.physicalCore Pa Pp ma ℓ γ gc hPa rfl htrace
    s.analyticAmbient s.physicalAmbient hg s.projectorCore
  exact ⟨{
    original := C
    cutoff := D
    originalSF := hC
    cutoffSF := hD
    retained := V
    badOriginal := BC
    badCutoff := BD
    retainedMeasurable := hV
    noReturnOriginal := hreturnC
    extinctOriginal := hextC
    noReturnCutoff := hreturnD
    extinctCutoff := hextD
    retainedKernelEq := heq
    originalData := dor
    cutoffData := dc
    rates := hrate
    retainedScalar := c
    retainedScalar_ne := hc
    retainedVectors := hret
    retainedVector_ne := hretne
    originalLeftMeasure := μoriginal
    originalLeftRep := hμoriginal
    probabilityProduct := hν
    cutoffLeftMeasure := μcut
    cutoffLeft_finite := inferInstance
    cutoffLeftRep := hμcut
    analyticAmbient := s.analyticAmbient
    physicalAmbient := s.physicalAmbient
    regularity := s.regularity
    positiveExponent := s.positiveExponent
    negativeExponent := s.negativeExponent
    regularOrder := s.regularOrder
    margins := s.margins
    analyticCore := s.analyticCore
    physicalCore := s.physicalCore
    analyticCore_dense := s.analyticCore_dense
    normalizedCore := s.normalizedCore
    analyticCore_action := s.analyticCore_action
    physicalCore_action := s.physicalCore_action
    projectorCore := s.projectorCore
    analyticScalar := a
    analyticScalar_ne := ha
    ambientVectors := hmatch
    analyticVector_ne := hane
    coreMultiplier := s.coreMultiplier
    multiplier_physical := s.multiplier_physical
    multiplier_analytic := s.multiplier_analytic }⟩

end ConditionedStochasticStabilityHyperbolic.ConstructedInvariantPairing
