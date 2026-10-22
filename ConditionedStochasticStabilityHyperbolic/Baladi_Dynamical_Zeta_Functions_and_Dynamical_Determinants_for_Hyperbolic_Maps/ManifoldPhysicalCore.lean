module

public import LeanShared.Geometry.ConstructedManifoldLocalization
public import LeanShared.Analysis.NormCompletionEquivalence
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.GlobalCompactEmbedding

/-!
# The literal manifold anisotropic core from a constructed partition

The finite chart partition and localization are constructed from a genuine
smooth adapted cover. The local source maps are the physical cone Fourier
blocks, with the supremum taken over the specified graph representation of
the paper's fake leaves. Their finite product closure therefore has exactly
the manuscript's maximum chart norm.
-/

@[expose] public noncomputable section

open MeasureTheory Set IsManifold
open scoped Manifold ContDiff SchwartzMap NNReal
attribute [local instance] Classical.propDecidable

namespace ConditionedStochasticStabilityHyperbolic.ManifoldPhysicalCore

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

/-- Each local map is the actual physical Fourier/leaf block norm map,
not an abstract supplied map into a Banach space. -/
def localBlocks (i : D.indices) := SchwartzAmbientBlocks.coreMap μ hL (leaves i)
  (ConstructedManifoldLocalization.support e D i)
  (ConeDyadicSymbols.symbols (radial i) (angle i)) (exponent i) (bounded i)

/-- The global smooth-core map applies physical blocks to the literal
cutoff functions in genuine chart coordinates. -/
def coreMap := ConstructedManifoldLocalization.chartCore e D he functions smooth
  (localBlocks e D μ hL leaves radial angle exponent bounded)

/-- Completion of the literal manuscript maximum chart norm. -/
abbrev Space := DyadicCompletion.closedCore
  (coreMap e D he functions smooth μ hL leaves radial angle exponent bounded)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- This is the exact maximum of local anisotropic Fourier/leaf norms in
the manuscript's definition of `B^{t,s}(T,V)`. -/
theorem norm_core (f : Core) :
    ‖DyadicCompletion.coreLift
      (coreMap e D he functions smooth μ hL leaves radial angle exponent bounded) f‖ =
    ((Finset.univ.sup (fun i => ‖localBlocks e D μ hL leaves radial angle exponent bounded i
      (ConstructedManifoldLocalization.localize e D he functions smooth i f)‖₊) : ℝ≥0) : ℝ) := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- Each local norm is exactly the weighted supremum over the specified
physical cone blocks and the specified ambient leaf family. -/
theorem local_norm (i : D.indices) (f : Core) :
    ‖localBlocks e D μ hL leaves radial angle exponent bounded i
      (ConstructedManifoldLocalization.localize e D he functions smooth i f)‖ =
    ⨆ j, ‖SchwartzAmbientBlocks.weightedBlock μ hL (leaves i)
      (ConstructedManifoldLocalization.support e D i)
      (ConeDyadicSymbols.symbols (radial i) (angle i)) (exponent i) j
      (ConstructedManifoldLocalization.localize e D he functions smooth i f)‖ := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- The coordinate entering those actual Fourier blocks is precisely
`(cutoff * f) ∘ chart⁻¹`, extended by zero. -/
theorem coordinate_formula (i : D.indices) (f : Core) (y : E) :
    (ConstructedManifoldLocalization.localize e D he functions smooth i f).val y =
      if y ∈ (e i).target then D.cutoff i ((e i).symm y) * functions f ((e i).symm y) else 0 := rfl

/-- The exact core chart coordinates consumed by the checked global compact
embedding producer, constructed from the same genuine localization. -/
def compactSourceCore := GlobalCompactEmbedding.strongChartMap
  (ConstructedManifoldLocalization.support e D)
  (localBlocks e D μ hL leaves radial angle exponent bounded)
  (ConstructedManifoldLocalization.localize e D he functions smooth)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- Passing local physical blocks into their closed cores changes no norm. -/
theorem compactSourceCore_norm (f : Core) :
    ‖compactSourceCore e D he functions smooth μ hL leaves radial angle exponent bounded f‖ =
      ‖coreMap e D he functions smooth μ hL leaves radial angle exponent bounded f‖ := rfl

/-- The manuscript completion and the actual source of the global compact
operator are canonically isometric. This identification is constructed from
the literal equal core norms, rather than assumed as a manifold interface. -/
def completionEquivalence :
    Space e D he functions smooth μ hL leaves radial angle exponent bounded ≃ₗᵢ[ℂ]
    DyadicCompletion.closedCore
      (compactSourceCore e D he functions smooth μ hL leaves radial angle exponent bounded) :=
  NormCompletionEquivalence.equivalence
    (coreMap e D he functions smooth μ hL leaves radial angle exponent bounded)
    (compactSourceCore e D he functions smooth μ hL leaves radial angle exponent bounded)
    (fun f => (compactSourceCore_norm e D he functions smooth μ hL leaves radial angle exponent bounded f).symm)

end ConditionedStochasticStabilityHyperbolic.ManifoldPhysicalCore
