module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ManifoldCompactEmbedding
public import LeanShared.Geometry.CompletedMicrolocalEstimate

/-!
# Canonical weak chart core for the actual manifold microscopic estimate

The weak row blocks are the constructed physical dyadic weakening of the
same local Fourier/leaf cores. Their global row core is definitionally the
target core of the actual manifold compact embedding. The canonical
inclusion has dense range because it maps every smooth core vector to the
same smooth weak core vector; no dense-range assumption is needed.
-/

@[expose] public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators
namespace ConditionedStochasticStabilityHyperbolic.ManifoldMicrolocalWeakCore
open LeanShared

variable {E U M AtlasIndex Core A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [AddCommGroup Core] [Module ℂ Core]
  (e : AtlasIndex → OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)
  (he : ∀ j, e j ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  (functions : Core →ₗ[ℂ] (M → ℂ))
  (smooth : ∀ f : Core, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (functions f))
  (μ : Measure U) [μ.IsAddHaarMeasure] {L : ℝ} (hL : 0 ≤ L)
  (leaves : D.indices → A → GraphLeafNorm.GraphLeaf U E L)
  {Cplus Cminus : D.indices → Set E}
  (radial : D.indices → ConeDyadicSymbols.RadialCutoff)
  (angle : ∀ i, ConeDyadicSymbols.AngularCutoff (Cplus i) (Cminus i))
  (exponent : D.indices → Bool → ℝ)
  (bounded : ∀ i, SchwartzAmbientBlocks.SmoothCoreBounded μ hL (leaves i)
    (ConstructedManifoldLocalization.support e D i)
    (ConeDyadicSymbols.symbols (radial i) (angle i)) (exponent i))


variable {loss : D.indices → ℝ} (positive : ∀ i, 0 < loss i)
  (extra : D.indices → Bool → ℝ) (nonnegative : ∀ i s, 0 ≤ extra i s)


/-- Actual weakened physical local block on the same supported input. -/
def localWeakBlocks (i : D.indices) :=
  (ManifoldCompactEmbedding.localOperator e D μ hL leaves radial angle exponent bounded positive extra nonnegative i).toLinearMap.comp
    (DyadicCompletion.coreLift (ManifoldPhysicalCore.localBlocks e D μ hL leaves radial angle exponent bounded i))

/-- The weak input vector used by the microscopic row estimate. -/
def rowWeakCore := CompletedMicrolocalEstimate.weakCore e D he functions smooth
  (localWeakBlocks e D μ hL leaves radial angle exponent bounded positive extra nonnegative)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- The microscopic norm is exactly the target physical completion core. -/
theorem rowWeakCore_eq :
    rowWeakCore e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative =
      ManifoldCompactEmbedding.weakCore e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- Both source and target norms are actual physical chart norms; smooth
core agreement proves dense range of their canonical completed inclusion. -/
theorem embedding_dense : DenseRange
    (ManifoldCompactEmbedding.embedding e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative) := by
  apply (DyadicCompletion.coreLift_dense
    (ManifoldCompactEmbedding.weakCore e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative)).mono
  rintro _ ⟨f, rfl⟩
  exact ⟨DyadicCompletion.coreLift
      (ManifoldPhysicalCore.coreMap e D he functions smooth μ hL leaves radial angle exponent bounded) f,
    ManifoldCompactEmbedding.embedding_core e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative f⟩


end ConditionedStochasticStabilityHyperbolic.ManifoldMicrolocalWeakCore
