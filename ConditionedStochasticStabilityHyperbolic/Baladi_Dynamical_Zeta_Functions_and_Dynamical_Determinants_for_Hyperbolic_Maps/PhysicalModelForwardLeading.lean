module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelSpectralLeading
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelTraceSetup
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelLeadingInputs
public import LeanShared.Dynamics.BasicHyperbolicFiniteWindowCoordinates
public import LeanShared.Geometry.FractionalSubunitComposition
meta import Lean.LibrarySuggestions.Basic

/-! The deterministic leading record of a physical model whose map sends the weight support into the
core region. The trace charts, the isometric framing, the regularized Lefschetz trace setup, the
regular seed of the weight and the reference pairing are all constructed; the remaining inputs
are the model data, the hyperbolic basic set, the compact two-norm estimate and the faithful
native test distribution with a constant-one test. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelForwardLeading"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff SchwartzMap Topology BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
  PhysicalModelAnalytic SchwartzJetSpace PhysicalModelFullTestPairing PhysicalModelLocalHolderTest
  PhysicalModelNativeCoefficients HyperbolicBasicSet FractionalManifoldRegularity
  ThermodynamicDefinitions

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

set_option maxHeartbeats 3200000 in
theorem spectral_leading_forward {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1)
    (lc : LocalCalculus m) (localBound : LocalPairing m bt) {L : ℝ} (bound : AnalyticBound m L)
    (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
    (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
    (physReg : Reg →L[ℂ] (M →ᵇ ℂ)) (hphys : ∀ r x, physReg r x = m.view r x)
    (β : m.localization.indices → M → ℝ)
    (hβ : ∀ j x, m.localization.cutoff j x = (β j x : ℂ))
    (hβs : ∀ j, ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ (β j)) (openV : IsOpen V)
    {T : M ≃ₜ M} {Λ : Set M} (bd : BasicData (E := E) T Λ V)
    (hT : (T : M → M) = m.maps a)
    (forwardSupport : (T : M → M) '' tsupport m.weight ⊆ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) (r : ℝ) (hr : 1 < r)
    (regular : Regular (E := E) (F := E) r T) (inverseRegular : Regular (E := E) (F := E) r T.symm)
    (mixing : MixingOn T Λ)
    (weightCont : Continuous m.weight) (weightNonneg : ∀ x, 0 ≤ m.weight x)
    (weightPos : ∀ x ∈ Λ, 0 < m.weight x) (weightSupport : ∀ x, m.weight x ≠ 0 → x ∈ closure V)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (weightRegular : Regular (E := E) (F := ℝ) q m.weight)
    (P0 : ℝ) (hP0 : pressure T (bd.hyperbolic.potential m.weight) Λ = (P0 : EReal))
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (i : m.StrongSpace →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ) (hα : 0 ≤ α) (hR' : 0 ≤ R) (hC : 0 ≤ C)
    (hD : 0 ≤ D)
    (twoNorm : ∀ n x, ‖((m.generator a) ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (gap : α < Real.exp P0)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (νE : Measure E) [νE.IsAddHaarMeasure]
    {Test : Type*} [NormedAddCommGroup Test] [NormedSpace ℂ Test]
    (aT : m.StrongSpace →L[ℂ] (Test →L[ℂ] ℂ)) (testView : Test → M →ᵇ ℂ)
    (core : ∀ c t, aT (coreLift m.qa c) t =
      ∫ x, SmoothSupportedManifoldCore.functions V c x * testView t x ∂(referenceMeasure.measure νE))
    (faithful : Function.Injective aT) (one : Test) (hone : ∀ x, testView one x = 1) :
    ∃ d : KellerLiverani1999.DeterministicLeading (m.generator a), d.rate = Real.exp P0 := by
  have mapCont : Continuous (m.maps a) := hT ▸ T.continuous
  have forward' : m.maps a '' tsupport m.weight ⊆ V := hT ▸ forwardSupport
  obtain ⟨tc, c', εc, εpos, c'smooth, c'nonneg, c'source, c'sum, partition, matched, cutOne⟩ :=
    trace_charts m a β hβ hβs mapCont openV forward'
  obtain ⟨frame, -⟩ := bd.exists_finite_window_coordinates forward inverse
  have coverΛ : ∀ x ∈ Λ, ∑ j, c' j x = 1 := fun x hx => by
    rw [← bd.hyperbolic.invariant] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact c'sum _ ⟨y, subset_tsupport _ (weightPos y hy).ne', by rw [← hT]⟩
  obtain ⟨s, e, hchart, hW, hcutoff, hrr⟩ := trace_setup m bd forward inverse r hr regular frame c'
    (fun j => (c'smooth j).continuous) c'nonneg c'source coverΛ weightCont weightNonneg weightPos
    weightSupport q hq0 hq1 (fun l => weightRegular.comp_iterate hq0 hq1 forward l)
  obtain ⟨seed, hseed⟩ := PhysicalModelLeadingInputs.seed_exists m a mapCont openV forward'
  obtain ⟨pairing, integral, hpair, hint⟩ := PhysicalModelLeadingInputs.reference_pairing m
    (referenceMeasure.measure νE) aT testView core physReg hphys one hone
  have integrableView : ∀ r, Integrable (m.view r) (referenceMeasure.measure νE) := fun r => by
    have := (physReg r).integrable (referenceMeasure.measure νE)
    have same : (⇑(physReg r) : M → ℂ) = m.view r := funext (hphys r)
    rwa [same] at this
  exact spectral_leading m tc hbt hbt1 lc localBound bound a strong remainder hs hR estimate
    (stdOrthonormalBasis ℝ E) physReg hphys mapCont partition bd s hT hW e hchart
    (fun j x hx => by rw [hcutoff j]; exact matched (e j) x hx) εc εpos
    (fun j z hz hne => cutOne (e j) z hz (by rw [hcutoff j] at hne; exact hne)) mixing
    (hrr ▸ inverseRegular) P0 hP0 i hi α R C D hα hR' hC hD twoNorm gap referenceMeasure νE aT
    testView core faithful pairing integral hpair hint integrableView seed hseed

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
