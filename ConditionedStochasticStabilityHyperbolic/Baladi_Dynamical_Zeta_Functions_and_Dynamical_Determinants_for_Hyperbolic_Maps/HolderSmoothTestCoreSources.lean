module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedSmoothTestCoreSources
public import LeanShared.Geometry.BoundedHolderMultiplication

/-! The supported little Hölder construction supplies the regular side of
the physical common core. Uniform evaluation and smooth multiplication are
derived; only the cited anisotropic pairing and multiplier facts are inputs. -/

public noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldSupportedCore
open LeanShared SmoothSupportedManifoldCore
variable {E M H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  (u : ℝ)
  (holder : ∀ c : core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)
  (V K : Set M) [CompactSpace K] (σ : Measure K)

def CoreData.of_holder_smooth_tests
    (qa : PhysicalManifoldModel.Core (E := E) V →ₗ[ℂ] H)
    (a : H →L[ℂ] (SmoothHolderTestSpaces.space u holder V →L[ℂ] ℂ))
    (pairing : ∀ c d, a (qa c) (SmoothHolderTestSpaces.coreMap u holder V d) =
      ∫ x : K, functions V c x.val * functions V d x.val ∂σ)
    (analyticBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖qa (multiplier V ψ hψ c)‖ ≤ B * ‖qa c‖) :
    CoreData (K := K) (Tests := SmoothPhysicalTests.tests (E := E) K) (σ := σ)
      (SmoothHolderTestSpaces.coreMap u holder V) qa := by
  apply CoreData.of_smooth_tests V K σ (SmoothHolderTestSpaces.coreMap u holder V) qa 1 ?_
    a pairing (SmoothHolderTestSpaces.smooth_multiplier_bound u holder V) analyticBound
  intro c
  rw [one_mul]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro x
  have h := ((SmoothHolderTestSpaces.physical u holder V
    (SmoothHolderTestSpaces.coreMap u holder V c)).norm_coe_le_norm x.val).trans
    (SmoothHolderTestSpaces.physical_norm_le u holder V (SmoothHolderTestSpaces.coreMap u holder V c))
  exact h

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldSupportedCore
