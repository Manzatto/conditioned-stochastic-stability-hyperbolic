module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeCoreData
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedSmoothTestCoreSources
meta import Lean.LibrarySuggestions.Basic

/-! The native supported-core packet (`CoreData`) of a physical model, from a
test-space distribution of the strong space with literal core values, a
regular-to-test inclusion, a uniform bound and the regular and analytic smooth
multiplier bounds. Its embedding is the composed distribution, so the
`smoothRestriction` identity holds by definition. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelNativeCorePacket"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelNativeCorePacket
open LeanShared DyadicCompletion PhysicalManifoldModel SmoothSupportedManifoldCore
  PhysicalModelNativeCoreData

variable {E U M AtlasIndex Reg A Ω Test : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  (ν : Measure M) (a : m.StrongSpace →L[ℂ] (Test →L[ℂ] ℂ)) (view : Test → M → ℂ)
  (core : ∀ c t, a (coreLift m.qa c) t = ∫ x, functions V c x * view t x ∂ν)
  (inc : Reg →L[ℂ] Test) (incView : ∀ r x, view (inc r) x = m.view r x)
  (K : Set M) [CompactSpace K] (hK : IsClosed K) (hVK : V ⊆ K)

/-- The native supported-core packet. -/
def coreData (C : ℝ) (uniform : ∀ c, ‖physicalCore V K c‖ ≤ C * ‖m.regularCore c‖)
    (regularBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖m.regularCore (multiplier V ψ hψ c)‖ ≤ B * ‖m.regularCore c‖)
    (analyticBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖coreLift m.qa (multiplier V ψ hψ c)‖ ≤ B * ‖coreLift m.qa c‖) :
    PhysicalManifoldSupportedCore.CoreData (K := K) (Tests := SmoothPhysicalTests.tests (E := E) K)
      (σ := ν.comap Subtype.val) m.regularCore (coreLift m.qa) :=
  { uniformConstant := C
    uniformBound := uniform
    embedding := regEmbedding m a inc
    smoothPairing := regEmbedding_pairing m ν a view core inc incView K hK hVK
    test := SmoothPhysicalTests.complexExtension K
    test_smooth := SmoothPhysicalTests.complexExtension_smooth K
    test_live := SmoothPhysicalTests.complexExtension_live K
    regularConstant := fun h =>
      Classical.choose (regularBound _ (SmoothPhysicalTests.complexExtension_smooth K h))
    analyticConstant := fun h =>
      Classical.choose (analyticBound _ (SmoothPhysicalTests.complexExtension_smooth K h))
    regularMultiplierBound := fun h =>
      Classical.choose_spec (regularBound _ (SmoothPhysicalTests.complexExtension_smooth K h))
    analyticMultiplierBound := fun h =>
      Classical.choose_spec (analyticBound _ (SmoothPhysicalTests.complexExtension_smooth K h)) }

theorem coreData_embedding (C : ℝ) (uniform : ∀ c, ‖physicalCore V K c‖ ≤ C * ‖m.regularCore c‖)
    (regularBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖m.regularCore (multiplier V ψ hψ c)‖ ≤ B * ‖m.regularCore c‖)
    (analyticBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖coreLift m.qa (multiplier V ψ hψ c)‖ ≤ B * ‖coreLift m.qa c‖)
    (z : m.StrongSpace) (r : Reg) :
    (coreData m ν a view core inc incView K hK hVK C uniform regularBound analyticBound).embedding z r =
      a z (inc r) := rfl

end ConditionedStochasticStabilityHyperbolic.PhysicalModelNativeCorePacket
