module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel
public import LeanShared.Analysis.NormCompletionEquivalence

/-! If the weak core of a model `m` has, vector by vector, the strong core
norms of a model `n`, the weak inclusion of `m` followed by the isometric
identification of completions is an inclusion `m.StrongSpace → n.StrongSpace`
which is the identity on the common smooth core and is compact whenever the
weak inclusion of `m` is. -/
@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelWeakTower
open LeanShared DyadicCompletion PhysicalManifoldModel

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
  (hnorm : ∀ c, ‖m.qW c‖ = ‖n.qa c‖)

def towerInclusion : m.StrongSpace →L[ℂ] n.StrongSpace :=
  (NormCompletionEquivalence.equivalence m.qW n.qa hnorm).toLinearIsometry.toContinuousLinearMap.comp
    m.inclusionW

theorem inclusionW_core (c : Core (E := E) V) :
    m.inclusionW (coreLift m.qa c) = coreLift m.qW c :=
  ManifoldCompactEmbedding.embedding_core m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossW_positive m.extraW m.extraW_nonnegative c

theorem towerInclusion_core (c : Core (E := E) V) :
    towerInclusion m n hnorm (coreLift m.qa c) = coreLift n.qa c :=
  (congrArg (NormCompletionEquivalence.equivalence m.qW n.qa hnorm) (inclusionW_core m c)).trans
    (NormCompletionEquivalence.equivalence_core _ _ _ c)

theorem towerInclusion_compact (compact : IsCompactOperator m.inclusionW) :
    IsCompactOperator (towerInclusion m n hnorm) :=
  compact.clm_comp _

theorem towerInclusion_norm (x : m.StrongSpace) :
    ‖towerInclusion m n hnorm x‖ = ‖m.inclusionW x‖ :=
  LinearIsometryEquiv.norm_map _ _

end ConditionedStochasticStabilityHyperbolic.PhysicalModelWeakTower
