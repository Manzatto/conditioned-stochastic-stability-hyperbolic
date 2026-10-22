module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel

/-! Chartwise compactness of the exact weakenings gives compactness of the
model's global strong-to-weak inclusion. -/
@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelCompactWeak
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
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

theorem inclusionW_isCompact
    (local_compact : ∀ i, IsCompactOperator (exactInclusion (m.localBlocks i) (m.lossW i)
      (m.lossW_positive i) (m.extraW i) (m.extraW_nonnegative i))) :
    IsCompactOperator m.inclusionW :=
  (FiniteChartCompletion.inclusion_isCompact
    (ManifoldCompactEmbedding.localOperator m.atlas m.localization μ m.slope_nonnegative m.leaves
      m.radial m.angle m.exponent m.boundedBlocks m.lossW_positive m.extraW m.extraW_nonnegative)
    (ManifoldCompactEmbedding.strongCore m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) μ
      m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks)
    local_compact).comp_clm
    (ManifoldPhysicalCore.completionEquivalence m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) μ
      m.slope_nonnegative m.leaves m.radial m.angle m.exponent
      m.boundedBlocks).toLinearIsometry.toContinuousLinearMap

end ConditionedStochasticStabilityHyperbolic.PhysicalModelCompactWeak
