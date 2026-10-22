module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ManifoldPhysicalCore
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ManifoldCompactEmbedding
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ManifoldMicrolocalWeakCore
public import LeanShared.Geometry.CompletedChartPairTransfer
public import LeanShared.Geometry.SmoothSupportedManifoldCore
public import LeanShared.Analysis.InvariantFiniteRegularCompatibility

/-! Primitive physical chart model for the literal supported manifold core.
The data are ordinary chart/leaf/Fourier and finite-Hölder facts. All spaces,
core maps, realizations and generators below are constructed definitions;
no compactness, global anisotropic operator bound or KL conclusion is a field. -/

@[expose] public noncomputable section
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

abbrev Core (V : Set M) := SmoothSupportedManifoldCore.core (E := E) V

structure Data (V S : Set M) (μ : Measure U) [μ.IsAddHaarMeasure] where
  atlas : AtlasIndex → OpenPartialHomeomorph M E
  localization : ConstructedManifoldLocalization.Data atlas S
  atlas_mem : ∀ j, atlas j ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M
  region_subset_support : V ⊆ S
  view : Reg →ₗ[ℂ] (M → ℂ)
  view_injective : Function.Injective view
  regularCore : Core (E := E) V →ₗ[ℂ] Reg
  regularCore_dense : DenseRange regularCore
  view_core : ∀ c, view (regularCore c) = SmoothSupportedManifoldCore.functions V c
  evaluate : M → Reg →L[ℂ] ℂ
  evaluation : ∀ x f, evaluate x f = view f x
  localView : ∀ i : localization.indices, LocalReg i.val →ₗ[ℂ] (E → ℂ)
  localView_injective : ∀ i, Function.Injective (localView i)
  localCore : ∀ i : localization.indices,
    SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support atlas localization i) →ₗ[ℂ] LocalReg i.val
  localCore_dense : ∀ i, DenseRange (localCore i)
  localView_core : ∀ i f, localView i (localCore i f) = f.val
  localEvaluate : ∀ i : localization.indices, E → LocalReg i.val →L[ℂ] ℂ
  localEvaluation : ∀ i x f, localEvaluate i x f = localView i f x
  coordinateConstant : localization.indices → ℝ
  coordinateBound : ∀ i c,
    ‖localCore i (ConstructedManifoldLocalization.localize atlas localization atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i c)‖ ≤
      coordinateConstant i * ‖regularCore c‖
  slope : ℝ
  slope_nonnegative : 0 ≤ slope
  leaves : localization.indices → A → GraphLeafNorm.GraphLeaf U E slope
  conePlus : localization.indices → Set E
  coneMinus : localization.indices → Set E
  radial : localization.indices → ConeDyadicSymbols.RadialCutoff
  angle : ∀ i, ConeDyadicSymbols.AngularCutoff (conePlus i) (coneMinus i)
  exponent : localization.indices → Bool → ℝ
  boundedBlocks : ∀ i, SchwartzAmbientBlocks.SmoothCoreBounded μ slope_nonnegative (leaves i)
    (ConstructedManifoldLocalization.support atlas localization i)
    (ConeDyadicSymbols.symbols (radial i) (angle i)) (exponent i)
  lossH : localization.indices → ℝ
  lossW : localization.indices → ℝ
  lossH_positive : ∀ i, 0 < lossH i
  lossW_positive : ∀ i, 0 < lossW i
  extraH : localization.indices → Bool → ℝ
  extraW : localization.indices → Bool → ℝ
  extraH_nonnegative : ∀ i b, 0 ≤ extraH i b
  extraW_nonnegative : ∀ i b, 0 ≤ extraW i b
  blockConstant : localization.indices → ℝ
  blockBound : ∀ i f,
    ‖ManifoldPhysicalCore.localBlocks atlas localization μ slope_nonnegative leaves radial angle exponent boundedBlocks i f‖ ≤
      blockConstant i * ‖localCore i f‖
  maps : Ω → M → M
  weight : M → ℝ
  invariant : ∀ a f, weightedComposition (maps a) weight (view f) ∈ view.range
  coreRegular : ∀ a (c : Core (E := E) V), weightedComposition (maps a) weight
    (SmoothSupportedManifoldCore.functions V c) ∈ view.range
  regularConstant : ℝ
  regularBound : ∀ a f,
    ‖InvariantFiniteRegularTransfer.action view view_injective maps weight invariant a f‖ ≤ regularConstant * ‖f‖

namespace Data

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

def localBlocks := ManifoldPhysicalCore.localBlocks m.atlas m.localization μ m.slope_nonnegative
  m.leaves m.radial m.angle m.exponent m.boundedBlocks

def qa := ManifoldPhysicalCore.coreMap m.atlas m.localization m.atlas_mem
  (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
  μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks

abbrev StrongSpace := closedCore m.qa

abbrev IntermediateSpace := ManifoldCompactEmbedding.WeakSpace m.atlas m.localization m.atlas_mem
  (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
  μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
  m.lossH_positive m.extraH m.extraH_nonnegative

abbrev WeakSpace := ManifoldCompactEmbedding.WeakSpace m.atlas m.localization m.atlas_mem
  (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
  μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
  m.lossW_positive m.extraW m.extraW_nonnegative

def qH := ManifoldCompactEmbedding.weakCore m.atlas m.localization m.atlas_mem
  (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
  μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
  m.lossH_positive m.extraH m.extraH_nonnegative

def qW := ManifoldCompactEmbedding.weakCore m.atlas m.localization m.atlas_mem
  (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
  μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
  m.lossW_positive m.extraW m.extraW_nonnegative

def weakLocalBlocksH := ManifoldMicrolocalWeakCore.localWeakBlocks m.atlas m.localization
  μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
  m.lossH_positive m.extraH m.extraH_nonnegative

def weakLocalBlocksW := ManifoldMicrolocalWeakCore.localWeakBlocks m.atlas m.localization
  μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
  m.lossW_positive m.extraW m.extraW_nonnegative

def inclusionH : m.StrongSpace →L[ℂ] m.IntermediateSpace :=
  ManifoldCompactEmbedding.embedding m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossH_positive m.extraH m.extraH_nonnegative

def inclusionW : m.StrongSpace →L[ℂ] m.WeakSpace :=
  ManifoldCompactEmbedding.embedding m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossW_positive m.extraW m.extraW_nonnegative

abbrev qReg := m.regularCore

def realize : Reg →L[ℂ] m.StrongSpace := CompletedChartPairTransfer.realization
  m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V)
  (SmoothSupportedManifoldCore.smooth V) m.regularCore m.regularCore_dense
  m.localCore m.localCore_dense m.coordinateConstant m.coordinateBound
  m.localBlocks m.blockConstant m.blockBound

def generator (a : Ω) : m.StrongSpace →L[ℂ] m.StrongSpace :=
  FiniteRegularTransferRealization.operator m.qa (SmoothSupportedManifoldCore.functions V)
    Reg m.view m.view_injective m.realize m.maps m.weight m.coreRegular a


end Data

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
