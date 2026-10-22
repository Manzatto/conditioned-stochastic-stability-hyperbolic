module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldWeakening

/-! Literal physical weaker exponents identify the canonical weak completion
with a fresh physical anisotropic model. This supplies the norm equality
needed to apply the analytic producer at a second admissible exponent pair. -/

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
open LeanShared DyadicCompletion CompletedChartPairTransfer FiniteRegularTransferRealization

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

namespace Data

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)


variable (loss : m.localization.indices → ℝ) (positive : ∀ i, 0 < loss i)
  (extra : m.localization.indices → Bool → ℝ) (nonnegative : ∀ i b, 0 ≤ extra i b)

/-- The actual inclusion with a fresh physical target, rather than a nested
subtype of the original block space. -/
@[expose] def loweredInclusion : m.StrongSpace →L[ℂ]
    closedCore (m.loweredCore loss positive extra nonnegative) :=
  (m.loweredEquivalence loss positive extra nonnegative).toLinearIsometry.toContinuousLinearMap.comp
    (ManifoldCompactEmbedding.embedding m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
      positive extra nonnegative)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
theorem loweredInclusion_core (c : Core (E := E) V) :
    m.loweredInclusion loss positive extra nonnegative (coreLift m.qa c) =
      coreLift (m.loweredCore loss positive extra nonnegative) c := by
  have h := ManifoldCompactEmbedding.embedding_core m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    positive extra nonnegative c
  exact (congrArg (m.loweredEquivalence loss positive extra nonnegative) h).trans
    (NormCompletionEquivalence.equivalence_core _ _ _ c)

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
