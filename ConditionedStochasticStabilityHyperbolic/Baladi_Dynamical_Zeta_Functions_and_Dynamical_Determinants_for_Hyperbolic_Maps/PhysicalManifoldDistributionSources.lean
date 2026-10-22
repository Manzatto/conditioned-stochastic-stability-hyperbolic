module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel

/-! Classical finite distribution-order sources on the literal local physical blocks.
The compact injective global inclusions are constructed from these sources;
no compactness or global inclusion is supplied as a field. -/

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldDistributionSources
open LeanShared LeanShared.DyadicCompletion LeanShared.CompletedChartPairTransfer
open LeanShared.FiniteRegularTransferRealization

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*}
  [∀ k, NormedAddCommGroup (LocalReg k)] [∀ k, NormedSpace ℂ (LocalReg k)]
  [∀ k, CompleteSpace (LocalReg k)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)


set_option maxHeartbeats 1600000 in
structure Data (Order : Type*) [Fintype Order] where
  words : m.localization.indices → Order → List E
  support : m.localization.indices → Set E
  compact_support : ∀ i, IsCompact (support i)
  cutoff : m.localization.indices → 𝓢(E, ℂ)
  supported : ∀ i y, y ∉ support i → cutoff i y = 0
  one : ∀ i y, y ∈ ConstructedManifoldLocalization.support m.atlas m.localization i → cutoff i y = 1
  pairing : ∀ i, closedCore (m.localBlocks i) →ₗ[ℂ] (𝓢(E, ℂ) →ₗ[ℂ] ℂ)
  constant : m.localization.indices → ℝ
  constant_nonnegative : ∀ i, 0 ≤ constant i
  bound : ∀ i b (f : 𝓢(E, ℂ)), (∀ x ∉ support i, f x = 0) →
    ‖pairing i b f‖ ≤ constant i * ‖b‖ * ‖SchwartzJetSpace.jetMap (support i) (words i) f‖
  core : ∀ i (f : SchwartzJetSpace.supportedCore
      (ConstructedManifoldLocalization.support m.atlas m.localization i)) (test : 𝓢(E, ℂ)),
    pairing i (coreLift (m.localBlocks i) f) test = ConeFourierBlocks.integralPairing f.val test

namespace Data
variable {Order : Type*} [Fintype Order] (d : Data m Order)

include d in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem compact_injective_H : IsCompactOperator m.inclusionH ∧ Function.Injective m.inclusionH :=
  ManifoldCompactEmbedding.compact_injective m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossH_positive m.extraH m.extraH_nonnegative d.words d.compact_support d.cutoff
    d.supported d.one d.pairing d.constant d.constant_nonnegative d.bound d.core

include d in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem compact_injective_W : IsCompactOperator m.inclusionW ∧ Function.Injective m.inclusionW :=
  ManifoldCompactEmbedding.compact_injective m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossW_positive m.extraW m.extraW_nonnegative d.words d.compact_support d.cutoff
    d.supported d.one d.pairing d.constant d.constant_nonnegative d.bound d.core

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldDistributionSources
