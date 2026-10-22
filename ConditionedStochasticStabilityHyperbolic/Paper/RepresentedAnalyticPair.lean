module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldPrimitivePair
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedCubeNoise

/-! Literal Whitney perturbations and their arbitrary bounded-density laws
feed the constructed physical manifold analytic pair. Model realization,
compactness, all spectral-estimate inputs and normalization rates are derived;
there is no separately supplied annealed family or law-convergence premise. -/

public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared KellerLiverani1999

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
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
  {Fiber : M → Type*} [∀ x, NormedAddCommGroup (Fiber x)]
  [∀ x, InnerProductSpace ℝ (Fiber x)] [∀ x, FiniteDimensional ℝ (Fiber x)]
  {Params : Type*} {I : ℕ → Type*} {Order : Type*} [Fintype Order]


variable {ι : Type*} [Fintype ι] {T : M ≃ₜ M} {r : ℝ}

@[expose] noncomputable def representedAnalyticPair
    (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
    (representation : Representation F Ω m.maps)
    (pS : PhysicalManifoldPrimitiveSources.Data (m.twoStepModel a b ha hb ea eb hea heb)
      (Fiber := Fiber) (Params := Params) (I := I) (Order := Order))
    (pH : PhysicalManifoldPrimitiveSources.Data (m.intermediateModel a b ha hb ea eb hea heb)
      (Fiber := Fiber) (Params := Params) (I := I) (Order := Order))
    (reference : representation.reference = pS.pressure.T)
    (referenceH : pH.pressure.T = pS.pressure.T)
    (weakS weakH R : ℝ)
    (hweakS : pS.pressure.ρ < weakS) (hweakH : pH.pressure.ρ < weakH)
    (hstepS : pS.rows.weakBound ≤ weakS) (hstepH : pH.rows.weakBound ≤ weakH)
    (hR : 1 ≤ R) (hρSR : pS.pressure.ρ < R) (hρHR : pH.pressure.ρ < R) :
    ProducedAnnealedPair.QuantitativeData (m.loweredInclusion a ha ea hea)
      (m.towerSecondInclusion a b ha hb ea eb hea heb) L.fixedLaw (fun _ => inferInstance)
      (fun ε z => (m.twoStepModel a b ha hb ea eb hea heb).generator (representation.fixedParameters ε z))
      (fun ε z => (m.intermediateModel a b ha hb ea eb hea heb).generator (representation.fixedParameters ε z))
      R pS.pressure.ρ pH.pressure.ρ weakS weakH := by
  apply PhysicalManifoldPrimitivePair.produced m a b ha hb ea eb hea heb pS pH referenceH
    representation.fixedParameters representation.fixedParameters_continuous representation.constant
    _ L.fixedLaw weakS weakH R hweakS hweakH hstepS hstepH hR hρSR hρHR
  intro ε z
  simpa only [← reference] using representation.fixedParameters_close ε z

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
