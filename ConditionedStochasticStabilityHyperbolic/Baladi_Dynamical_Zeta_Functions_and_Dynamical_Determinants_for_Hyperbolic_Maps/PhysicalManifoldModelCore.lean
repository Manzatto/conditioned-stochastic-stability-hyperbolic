module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel

/-! Exact core identities for the constructed physical manifold model. -/

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

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
private theorem inclusionH_core (c : Core (E := E) V) :
    m.inclusionH (coreLift m.qa c) = coreLift m.qH c :=
  ManifoldCompactEmbedding.embedding_core m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossH_positive m.extraH m.extraH_nonnegative c

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
private theorem inclusionW_core (c : Core (E := E) V) :
    m.inclusionW (coreLift m.qa c) = coreLift m.qW c :=
  ManifoldCompactEmbedding.embedding_core m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossW_positive m.extraW m.extraW_nonnegative c

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
private theorem weakLocalBlocksH_coreMap : CompletedChartPairTransfer.coreMap
    m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V)
    (SmoothSupportedManifoldCore.smooth V) m.weakLocalBlocksH = m.qH :=
  ManifoldMicrolocalWeakCore.rowWeakCore_eq m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossH_positive m.extraH m.extraH_nonnegative

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
private theorem weakLocalBlocksW_coreMap : CompletedChartPairTransfer.coreMap
    m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V)
    (SmoothSupportedManifoldCore.smooth V) m.weakLocalBlocksW = m.qW :=
  ManifoldMicrolocalWeakCore.rowWeakCore_eq m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossW_positive m.extraW m.extraW_nonnegative


omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- The source realization agrees with the literal physical chart core. -/
theorem realize_core (c : Core (E := E) V) : m.realize (m.qReg c) = coreLift m.qa c :=
  CompletedChartPairTransfer.realization_core m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    m.regularCore m.regularCore_dense m.localCore m.localCore_dense
    m.coordinateConstant m.coordinateBound m.localBlocks m.blockConstant m.blockBound c

include m in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
/-- Source support follows from the actual supported core and the geometric inclusion. -/
theorem core_zero_outside (c : Core (E := E) V) (x : M) (hx : x ∉ S) :
    SmoothSupportedManifoldCore.functions V c x = 0 :=
  SmoothSupportedManifoldCore.zero_outside V c x (fun hv => hx (m.region_subset_support hv))


end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
