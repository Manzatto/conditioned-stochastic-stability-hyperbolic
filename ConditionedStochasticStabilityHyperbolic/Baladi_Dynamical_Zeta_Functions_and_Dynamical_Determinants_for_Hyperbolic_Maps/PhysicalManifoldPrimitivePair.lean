module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldPairedInputs
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldPrimitiveSources

/-! Two complete ordinary manifold source records produce the actual
quantitative KL pair. Compactness, intrinsic finite-block estimates,
mixed-norm perturbation and cross-generator compatibility are all derived. -/

public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPrimitivePair
open LeanShared KellerLiverani1999

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
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

@[expose] noncomputable def produced
    (pS : PhysicalManifoldPrimitiveSources.Data (m.twoStepModel a b ha hb ea eb hea heb)
      (Fiber := Fiber) (Params := Params) (I := I) (Order := Order))
    (pH : PhysicalManifoldPrimitiveSources.Data (m.intermediateModel a b ha hb ea eb hea heb)
      (Fiber := Fiber) (Params := Params) (I := I) (Order := Order))
    (reference : pH.pressure.T = pS.pressure.T)
    {Noise : Type*} [TopologicalSpace Noise] [MeasurableSpace Noise]
    [OpensMeasurableSpace Noise] [SecondCountableTopology Noise]
    (noise : ℝ≥0 → Noise → Ω) (continuous_noise : ∀ ε, Continuous (noise ε))
    (C : ℝ) (close : ∀ ε z, dist (noise ε z) pS.pressure.T ≤ C * (ε : ℝ))
    (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)]
    (weakS weakH R : ℝ)
    (hweakS : pS.pressure.ρ < weakS) (hweakH : pH.pressure.ρ < weakH)
    (hstepS : pS.rows.weakBound ≤ weakS) (hstepH : pH.rows.weakBound ≤ weakH)
    (hR : 1 ≤ R) (hρSR : pS.pressure.ρ < R) (hρHR : pH.pressure.ρ < R) :
    ProducedAnnealedPair.QuantitativeData (m.loweredInclusion a ha ea hea)
      (m.towerSecondInclusion a b ha hb ea eb hea heb) law (fun _ => inferInstance)
      (fun ε z => (m.twoStepModel a b ha hb ea eb hea heb).generator (noise ε z))
      (fun ε z => (m.intermediateModel a b ha hb ea eb hea heb).generator (noise ε z))
      R pS.pressure.ρ pH.pressure.ρ weakS weakH := by
  have closeH : ∀ ε z, dist (noise ε z) pH.pressure.T ≤ C * (ε : ℝ) := by
    simpa only [reference] using close
  have hρS : 0 < pS.pressure.ρ := lt_of_le_of_lt
    (ge_of_tendsto' pS.pressure.pressure (fun N => Real.rpow_nonneg (DomainPressureRefinement.coverCoefficient_nonneg_of_bdd
      (pS.pressure.bounded N) (pS.pressure.cover N)) _)) pS.pressure.slack
  have hρH : 0 < pH.pressure.ρ := lt_of_le_of_lt
    (ge_of_tendsto' pH.pressure.pressure (fun N => Real.rpow_nonneg (DomainPressureRefinement.coverCoefficient_nonneg_of_bdd
      (pH.pressure.bounded N) (pH.pressure.cover N)) _)) pH.pressure.slack
  let strong := pS.actualModel (m.twoStepModel a b ha hb ea eb hea heb)
    noise continuous_noise C close law weakS R hρS hweakS hstepS hR hρSR
  let middle := pH.actualModel (m.intermediateModel a b ha hb ea eb hea heb)
    noise continuous_noise C closeH law weakH R hρH hweakH hstepH hR hρHR
  exact PhysicalManifoldPairedInputs.producedQuantitative m a b ha hb ea eb hea heb
    law noise R pS.rows pH.rows strong middle

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPrimitivePair
