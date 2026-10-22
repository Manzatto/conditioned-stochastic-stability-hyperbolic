module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalHolderClassicalSources
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.HolderSmoothTestCoreSources
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedSmoothTestCoreSources

/-! Literal smooth-test metadata of the ordinary Holder core factory. These
identities let applications use the chosen smooth extension without unfolding
all embeddings, bounds and dense-core fields of the produced core packet. -/
public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PhysicalHolderClassicalSources
open LeanShared DyadicCompletion SmoothSupportedManifoldCore
variable {E U M AtlasIndex A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

variable (u : ℝ)
  (holder : ∀ c : core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)


variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M)
    (AtlasIndex := AtlasIndex) (Reg := Regular u holder V) (LocalReg := LocalReg)
    (A := A) (Ω := Ω) V S μ)
  (K : Set M) [CompactSpace K] (σ : Measure K) [IsFiniteMeasure σ]

namespace SourceData
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  {qa : core (E := E) V →ₗ[ℂ] H}
  (s : SourceData u holder m K σ qa)


omit [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M]
  [∀ i, CompleteSpace (LocalReg i)] [IsFiniteMeasure σ] in
/-- The core factory uses exactly the canonical global smooth extension. -/
@[simp] theorem coreData_test (ψ : SmoothPhysicalTests.tests (E := E) K) :
    (s.coreData u holder m K σ).test ψ = SmoothPhysicalTests.complexExtension K ψ := by
  rfl

omit [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M]
  [∀ i, CompleteSpace (LocalReg i)] [IsFiniteMeasure σ] in
/-- Both the multiplier function and its smoothness witness agree; no
additional multiplier compatibility is a background input. -/
@[simp] theorem coreData_multiplier (ψ : SmoothPhysicalTests.tests (E := E) K) :
    multiplier V ((s.coreData u holder m K σ).test ψ)
      ((s.coreData u holder m K σ).test_smooth ψ) =
    multiplier V (SmoothPhysicalTests.complexExtension K ψ)
      (SmoothPhysicalTests.complexExtension_smooth K ψ) := by
  rfl

end SourceData
end ConditionedStochasticStabilityHyperbolic.PhysicalHolderClassicalSources
