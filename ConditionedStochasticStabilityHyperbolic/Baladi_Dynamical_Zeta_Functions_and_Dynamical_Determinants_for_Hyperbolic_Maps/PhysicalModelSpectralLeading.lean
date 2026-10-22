module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelTraceLeading
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeRadiusUpper
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelPositiveCone
public import LeanShared.Dynamics.BasicHyperbolicOrbitIntegralGrowth
public import LeanShared.Geometry.FiniteSmoothReferenceMeasure
meta import Lean.LibrarySuggestions.Basic

/-! The deterministic leading record of the carrier generator at the pressure rate. The orbit
integral growth at the pressure bounds the spectral radius by `e^P`, the positive cone puts
`e^P` in the spectrum, and the regularized traces give the separated rank-one leading
projection. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelSpectralLeading"

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
theorem spectral_leading (tc : TraceCharts m) {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1)
    (lc : LocalCalculus m) (localBound : LocalPairing m bt) {L : ℝ} (bound : AnalyticBound m L)
    (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
    (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (physReg : Reg →L[ℂ] (M →ᵇ ℂ)) (hphys : ∀ r x, physReg r x = m.view r x)
    (mapCont : Continuous (m.maps a))
    (partition : ∀ x, m.weight x ≠ 0 → (∑ j : m.localization.indices,
      if m.maps a x ∈ (m.atlas j).source then
        tc.wt j (m.atlas j (m.maps a x)) * m.localization.cutoff j (m.maps a x) else 0) = 1)
    {T : M ≃ₜ M} {Λ : Set M} (bd : BasicData (E := E) T Λ V) (s : TraceSetup bd)
    (hT : (T : M → M) = m.maps a) (hW : s.weight = m.weight)
    (e : s.charts.ι ≃ m.localization.indices) (hchart : ∀ i, s.charts.chart i = m.atlas (e i))
    (hc : ∀ i, ∀ x ∈ (m.atlas (e i)).source,
      (s.cutoff i x : ℂ) = m.localization.cutoff (e i) x * tc.wt (e i) (m.atlas (e i) x))
    (εc : ℝ) (hεc : 0 < εc)
    (hcut : ∀ i, ∀ z ∈ (m.atlas (e i)).target, s.cutoff i ((m.atlas (e i)).symm z) ≠ 0 →
      ∀ u, ‖u - z‖ ≤ εc → tc.cut (e i) u = 1)
    (mixing : MixingOn T Λ) (inverseRegular : Regular (E := E) (F := E) s.r T.symm)
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
    (faithful : Function.Injective aT)
    (pairing : m.StrongSpace →L[ℂ] ℂ) (integral : Reg →L[ℂ] ℂ)
    (hpair : ∀ r, pairing (m.realize r) = integral r)
    (hint : ∀ r, integral r = ∫ x, m.view r x ∂(referenceMeasure.measure νE))
    (integrableView : ∀ r, Integrable (m.view r) (referenceMeasure.measure νE))
    (seed : Reg) (hseed : ∀ x, m.view seed x = (m.weight x : ℂ)) :
    ∃ d : KellerLiverani1999.DeterministicLeading (m.generator a), d.rate = Real.exp P0 := by
  have weightCont : Continuous m.weight := hW ▸ s.weight_continuous
  have nonnegative : ∀ x, 0 ≤ m.weight x := hW ▸ s.weight_nonneg
  have positiveW : ∀ x ∈ Λ, 0 < m.weight x := hW ▸ s.weight_pos
  have supported : Function.support m.weight ⊆ closure V := fun x hx =>
    s.weight_support x (by rw [hW]; exact hx)
  have regularW : Regular (E := E) (F := ℝ) s.q m.weight := hW ▸ s.weight_regular 0
  have upper : ∀ R' : ℝ, Real.exp P0 < R' → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (∫⁻ x, ENNReal.ofReal
      (∏ j ∈ Finset.range n, m.weight ((m.maps a)^[j] x)) ∂(referenceMeasure.measure νE)) ≤
      ENNReal.ofReal (C * R' ^ n) := fun R' hR'' => by
    rw [← hT]
    exact bd.orbit_integral_growth_at_pressure s.forward s.inverse m.weight weightCont positiveW
      nonnegative supported referenceMeasure νE P0 hP0 R' hR''
  have radius : spectralRadius ℂ (m.generator a) ≤ ENNReal.ofReal (Real.exp P0) :=
    PhysicalModelNativeRadiusUpper.spectralRadius_le m (referenceMeasure.measure νE) aT testView
      core physReg hphys bound a faithful i hi α R C D hα hR' hC hD twoNorm nonnegative
      (Real.exp P0) (Real.exp_pos P0) gap.le upper
  have positive : ((Real.exp P0 : ℝ) : ℂ) ∈ spectrum ℂ (m.generator a) :=
    PhysicalModelPositiveCone.exp_pressure_mem_spectrum m bound T Λ bd s.one_lt_r s.q_pos s.regular
      inverseRegular mixing referenceMeasure νE regularW positiveW nonnegative P0 hP0 a hT.symm
      pairing integral hpair hint integrableView seed hseed radius
  exact deterministic_leading m tc hbt hbt1 lc localBound bound a strong remainder hs hR estimate b
    physReg hphys weightCont mapCont partition bd s hT hW e hchart hc εc hεc hcut mixing
    inverseRegular P0 (by rw [hW]; exact hP0) i hi α R C D hα hR' hC hD twoNorm gap radius positive

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
