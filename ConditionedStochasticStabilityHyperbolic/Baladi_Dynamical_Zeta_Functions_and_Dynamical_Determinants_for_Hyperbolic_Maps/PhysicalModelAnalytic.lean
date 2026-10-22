module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelUniformBounds
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCompatibility
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldNoiseSources

/-! A uniform one-step core bound (`AnalyticBound`) gives the operator bound,
the literal core formula of every constructed generator, continuity of the
generators on the core along the letter space, and intertwining with a second
model sharing the ordinary data. -/
@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelAnalytic
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
open FiniteRegularTransferRealization

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
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m n : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

/-- The uniform one-step bound of the literal core actions. -/
def AnalyticBound (L : ℝ) : Prop :=
  ∀ a c, ‖targetCore m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
    m.realize m.maps m.weight m.coreRegular a c‖ ≤ L * ‖m.qa c‖

theorem analytic_of_estimates (Smax : ℝ)
    (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hR : ∀ i j, 0 ≤ remainder i j)
    (estimates : ∀ a, ∃ strong, 0 ≤ strong ∧ strong ≤ Smax ∧
      PairEstimate m (m.maps a) m.weight strong remainder) :
    AnalyticBound m (oneStepConstant m Smax remainder) :=
  PhysicalModelUniformBounds.analytic_of_estimates m Smax remainder hR estimates

theorem generatorBound {L : ℝ} (bound : AnalyticBound m L) (hL : 0 ≤ L) :
    GeneratorBound m L := fun a =>
  operator_norm_le m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
    m.realize m.maps m.weight m.coreRegular L bound hL a

theorem generator_core {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (c : Core (E := E) V) :
    m.generator a (coreLift m.qa c) = m.realize (regularAction (SmoothSupportedManifoldCore.functions V)
      Reg m.view m.view_injective m.maps m.weight m.coreRegular a c) :=
  operator_core m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
    m.realize m.maps m.weight m.coreRegular L bound a c

theorem core_continuous [MetricSpace Ω] {L : ℝ} (bound : AnalyticBound m L)
    (sources : PhysicalManifoldNoiseSources.Data m) (c : Core (E := E) V) :
    Continuous (fun a => m.generator a (coreLift m.qa c)) := by
  have same : (fun a => m.generator a (coreLift m.qa c)) = fun a =>
      m.realize (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view
        m.view_injective m.maps m.weight m.coreRegular a c) :=
    funext fun a => generator_core m bound a c
  rw [same]
  exact m.realize.continuous.comp (sources.core_continuous m c)

/-- Intertwining of the generators of two models sharing the ordinary data. -/
theorem intertwining (hreg : m.regularCore = n.regularCore) (hview : m.view = n.view)
    (hmaps : m.maps = n.maps) (hweight : m.weight = n.weight)
    (j : m.StrongSpace →L[ℂ] n.StrongSpace) (hcore : ∀ c, j (coreLift m.qa c) = coreLift n.qa c)
    {Lm Ln : ℝ} (boundM : AnalyticBound m Lm) (boundN : AnalyticBound n Ln) (a : Ω)
    (x : m.StrongSpace) : j (m.generator a x) = n.generator a (j x) :=
  DFunLike.congr_fun ((PhysicalModelCompatibility.compatibleOperators m n hreg hview hmaps hweight
    j hcore (generator_core m boundM) (generator_core n boundN)).generator a) x

end ConditionedStochasticStabilityHyperbolic.PhysicalModelAnalytic
