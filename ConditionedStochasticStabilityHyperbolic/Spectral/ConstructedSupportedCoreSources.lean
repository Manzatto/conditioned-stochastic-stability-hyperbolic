module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ConstructedInvariantPairing
public import ConditionedStochasticStabilityHyperbolic.Spectral.ConstructedRegularMultipliers

/-! Invariant supported-core inputs from a constructed little-Cu realization.
All whole-regular-space action, projector and multiplication identities follow
by density from literal smooth functions. Classical inputs are ordinary and
anisotropic norm bounds, supported smooth approximation, faithful distribution
embedding, and SAME-cutoff Riesz projector comparison on smooth functions. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedSupportedCoreSources
open RegularCoreApproximation ConstructedRegularMultipliers

variable {Reg H Z Smooth X : Type*}
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [AddCommGroup Smooth] [Module ℂ Smooth]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

variable (D : Realization (Reg := Reg) (A := H) (Core := Smooth) (X := X))
  (q : Smooth →ₗ[ℂ] Reg) (hq : ∀ c, q c = D.smooth c)
  (qa : Smooth →ₗ[ℂ] H) (hqa : DenseRange qa)
  (ha : ∀ c, D.analytic (D.smooth c) = qa c)

include hqa ha in
omit [CompleteSpace Reg] [CompleteSpace H] [MeasurableSpace X] [BorelSpace X] in
theorem analytic_dense : DenseRange D.analytic := by
  apply hqa.mono
  rintro y ⟨c, rfl⟩
  exact ⟨D.smooth c, ha c⟩

variable (A : Set (X →ᵇ ℝ)) (multiply : A → Smooth →ₗ[ℂ] Smooth)
  (raw : Smooth →ₗ[ℂ] (X → ℂ))
  (hphysical : ∀ c x, D.physical (D.smooth c) x = raw c x)
  (hmultiply : ∀ (h : A) c x, raw (multiply h c) x = raw c x * (h.val x : ℂ))
  (CR CA : A → ℝ) (hCR : ∀ h, 0 ≤ CR h) (hCA : ∀ h, 0 ≤ CA h)
  (hregular : ∀ (h : A) c, ‖q (multiply h c)‖ ≤ CR h * ‖q c‖)
  (hanalytic : ∀ (h : A) c, ‖qa (multiply h c)‖ ≤ CA h * ‖qa c‖)

include hphysical hmultiply in
omit [CompleteSpace Reg] [CompleteSpace H] [MeasurableSpace X] [BorelSpace X] in
theorem physical_smooth_multiplier (h : A) (c : Smooth) :
    D.physical (D.smooth (multiply h c)) = D.physical (D.smooth c) *
      AbsorbingMarkovChains.ComplexKernel.ofReal h.val := by
  ext x
  simp only [BoundedContinuousFunction.mul_apply, AbsorbingMarkovChains.ComplexKernel.ofReal_apply,
    hphysical, hmultiply]

/-- Every whole-space invariant-core field is constructed. The actual core
is the little regular completion, with its ordinary and anisotropic maps. -/
def coreSourcesOfSmoothFacts
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (dc : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF)
      (1 : X →ᵇ ℝ)) (μ : Measure X) [IsFiniteMeasure μ]
    (Pa Pm : H →L[ℂ] H) (leadingRate : ℝ) (hrate : dc.rate = leadingRate)
    (T : Reg →L[ℂ] Reg)
    (hanalyticAction : ∀ c, D.analytic (T (D.smooth c)) = Pm (D.analytic (D.smooth c)))
    (hphysicalAction : ∀ c, D.physical (T (D.smooth c)) =
      ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF (D.physical (D.smooth c)))
    (a : H →L[ℂ] Z) (b : (X →ᵇ ℂ) →L[ℂ] Z) (O : Set X)
    (hsupportedDense : ∀ f : X →ᵇ ℂ, tsupport f ⊆ O →
      f ∈ closure (range (fun c => D.physical (D.smooth c))))
    (hfaithful : ∀ f : X →ᵇ ℂ, tsupport f ⊆ O → b f = 0 → f = 0)
    (hprojector : ∀ c, b ((ComplexLeadingMeasure.integralFunctional μ).smulRight
      (AbsorbingMarkovChains.ComplexKernel.ofReal dc.eigenvector) (D.physical (D.smooth c))) =
      a (Pa (D.analytic (D.smooth c))))
    (r t s u : ℝ) (hmargins : RegularityMargins r t s u) :
    ConstructedInvariantPairing.CoreSources (Z := Z) (Core := Reg)
      Pa ((leadingRate : ℂ)⁻¹ • Pm) C hSF dc μ A (fun h => analyticMultiplier qa (multiply h)) := by
  have hactionA : D.analytic.comp T = Pm.comp D.analytic := by
    apply ContinuousLinearMap.ext
    intro v
    exact D.dense.induction_on
      (p := fun v => D.analytic (T v) = Pm (D.analytic v)) v
      (isClosed_eq (D.analytic.continuous.comp T.continuous) (Pm.continuous.comp D.analytic.continuous))
      hanalyticAction
  have hactionP : D.physical.comp T =
      (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF).comp D.physical := by
    apply ContinuousLinearMap.ext
    intro v
    exact D.dense.induction_on
      (p := fun v => D.physical (T v) = ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF (D.physical v)) v
      (isClosed_eq (D.physical.continuous.comp T.continuous)
        ((ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF).continuous.comp D.physical.continuous))
      hphysicalAction
  refine {
    analyticAmbient := a
    physicalAmbient := b
    supportedRegion := O
    regularity := r
    positiveExponent := t
    negativeExponent := s
    regularOrder := u
    margins := hmargins
    analyticCore := D.analytic
    physicalCore := D.physical
    supportedCoreDensity := ?_
    supportedFaithful := hfaithful
    analyticCore_dense := analytic_dense D qa hqa ha
    normalizedCore := (leadingRate : ℂ)⁻¹ • T
    analyticCore_action := ?_
    physicalCore_action := ?_
    projectorCore := ?_
    coreMultiplier := fun h => regularMultiplier q (multiply h)
    multiplier_physical := ?_
    multiplier_analytic := ?_ }
  · intro f hf
    apply closure_mono _ (hsupportedDense f hf)
    rintro y ⟨c, rfl⟩
    exact ⟨D.smooth c, rfl⟩
  · apply ContinuousLinearMap.ext
    intro v
    have hh := congrArg (fun L : Reg →L[ℂ] H => L v) hactionA
    simpa only [ContinuousLinearMap.comp_apply, smul_apply, map_smul] using congrArg ((leadingRate : ℂ)⁻¹ • ·) hh
  · apply ContinuousLinearMap.ext
    intro v
    have hh := congrArg (fun L : Reg →L[ℂ] (X →ᵇ ℂ) => L v) hactionP
    simpa only [ContinuousLinearMap.comp_apply, smul_apply, map_smul, hrate] using congrArg ((leadingRate : ℂ)⁻¹ • ·) hh
  · intro v
    let Pp := (ComplexLeadingMeasure.integralFunctional μ).smulRight
      (AbsorbingMarkovChains.ComplexKernel.ofReal dc.eigenvector)
    exact D.dense.induction_on (p := fun v => b (Pp (D.physical v)) = a (Pa (D.analytic v))) v
      (isClosed_eq (b.continuous.comp (Pp.continuous.comp D.physical.continuous))
        (a.continuous.comp (Pa.continuous.comp D.analytic.continuous))) hprojector
  · intro h v
    exact physical_multiplier_law D q hq (multiply h) h.val
      (physical_smooth_multiplier D A multiply raw hphysical hmultiply h)
      (CR h) (hregular h) v
  · intro h
    exact analytic_multiplier_law D q hq qa hqa ha (multiply h)
      (CR h) (CA h) (hregular h) (hanalytic h)

end ConditionedStochasticStabilityHyperbolic.ConstructedSupportedCoreSources
