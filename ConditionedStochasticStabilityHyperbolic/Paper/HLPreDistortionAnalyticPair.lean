module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionPrimitiveSources
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedAnalyticPair
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedCubeNoise

/-! Ordinary HL sources BEFORE random control robustness and separate-to-joint distortion, literal Whitney perturbations and arbitrary bounded-density laws
feed the constructed physical manifold analytic pair. Model realization,
compactness, all spectral-estimate inputs and normalization rates are derived;
there is no separately supplied annealed family or law-convergence premise. -/

public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff SchwartzMap BigOperators NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionAnalyticPair
open LeanShared KellerLiverani1999 Paper.RegularNoise

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

variable (a b : m.localization.indices → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
  (ea eb : m.localization.indices → Bool → ℝ)
  (hea : ∀ i j, 0 ≤ ea i j) (heb : ∀ i j, 0 ≤ eb i j)



variable [MetricSpace Ω]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {Order : Type*} [Fintype Order]


variable {ι : Type*} [Fintype ι] {T : M ≃ₜ M} {g : M → ℝ} {Λ : Set M}
  (h : Paper.HL (E := E) T g Λ V)

@[expose] noncomputable def produced
    (F : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
    (representation : Representation F Ω m.maps)
    (sS : HLPreDistortionPrimitiveSources.Data (m.twoStepModel a b ha hb ea eb hea heb) h
      (Order := Order))
    (sH : HLPreDistortionPrimitiveSources.Data (m.intermediateModel a b ha hb ea eb hea heb) h
      (Order := Order))
    (reference : representation.reference = sS.pressure.reference)
    (referenceH : sH.pressure.reference = sS.pressure.reference)
    (weakS weakH R : ℝ)
    (hweakS : (sS.primitive _ h).pressure.ρ < weakS) (hweakH : (sH.primitive _ h).pressure.ρ < weakH)
    (hstepS : sS.rows.weakBound ≤ weakS) (hstepH : sH.rows.weakBound ≤ weakH)
    (hR : 1 ≤ R) (hρSR : (sS.primitive _ h).pressure.ρ < R) (hρHR : (sH.primitive _ h).pressure.ρ < R) :
    ProducedAnnealedPair.QuantitativeData (m.loweredInclusion a ha ea hea)
      (m.towerSecondInclusion a b ha hb ea eb hea heb) L.fixedLaw (fun _ => inferInstance)
      (fun ε z => (m.twoStepModel a b ha hb ea eb hea heb).generator (representation.fixedParameters ε z))
      (fun ε z => (m.intermediateModel a b ha hb ea eb hea heb).generator (representation.fixedParameters ε z))
      R (sS.primitive _ h).pressure.ρ (sH.primitive _ h).pressure.ρ weakS weakH := by
  let pS := sS.primitive _ h
  let pH := sH.primitive _ h
  exact RegularNoise.representedAnalyticPair m a b ha hb ea eb hea heb F L representation pS pH
    (reference.trans (sS.principal_reference _ h).symm)
    ((sH.principal_reference _ h).trans (referenceH.trans (sS.principal_reference _ h).symm))
    weakS weakH R hweakS hweakH hstepS hstepH hR hρSR hρHR

end ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionAnalyticPair
