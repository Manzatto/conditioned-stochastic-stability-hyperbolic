module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldSupportedCore
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.SmoothPhysicalTests

/-! The common-core packet uses the constructed dense smooth test set.
Ordinary Cu and anisotropic smooth multiplication bounds select all scalar
constants; no supplied test extension, test density or multiplier operator
is retained. -/

public noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldSupportedCore
open LeanShared SmoothSupportedManifoldCore
variable {E M Reg H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  (V K : Set M) [CompactSpace K] (σ : Measure K)

def CoreData.of_smooth_tests
    (q : PhysicalManifoldModel.Core (E := E) V →ₗ[ℂ] Reg)
    (qa : PhysicalManifoldModel.Core (E := E) V →ₗ[ℂ] H)
    (C : ℝ) (uniform : ∀ c, ‖physicalCore V K c‖ ≤ C * ‖q c‖)
    (a : H →L[ℂ] (Reg →L[ℂ] ℂ))
    (pairing : ∀ c d, a (qa c) (q d) = ∫ x : K, functions V c x.val * functions V d x.val ∂σ)
    (regularBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖q (multiplier V ψ hψ c)‖ ≤ B * ‖q c‖)
    (analyticBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖qa (multiplier V ψ hψ c)‖ ≤ B * ‖qa c‖) :
    CoreData (K := K) (Tests := SmoothPhysicalTests.tests (E := E) K) (σ := σ) q qa where
  uniformConstant := C
  uniformBound := uniform
  embedding := a
  smoothPairing := pairing
  test := SmoothPhysicalTests.complexExtension K
  test_smooth := SmoothPhysicalTests.complexExtension_smooth K
  test_live := SmoothPhysicalTests.complexExtension_live K
  regularConstant := fun h => Classical.choose (regularBound _ (SmoothPhysicalTests.complexExtension_smooth K h))
  analyticConstant := fun h => Classical.choose (analyticBound _ (SmoothPhysicalTests.complexExtension_smooth K h))
  regularMultiplierBound := fun h => Classical.choose_spec (regularBound _ (SmoothPhysicalTests.complexExtension_smooth K h))
  analyticMultiplierBound := fun h => Classical.choose_spec (analyticBound _ (SmoothPhysicalTests.complexExtension_smooth K h))

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldSupportedCore
