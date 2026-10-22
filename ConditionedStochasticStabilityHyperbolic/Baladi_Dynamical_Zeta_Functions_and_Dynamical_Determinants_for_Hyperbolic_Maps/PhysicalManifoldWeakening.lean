module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel
public import LeanShared.Analysis.NormCompletionEquivalence

/-! Literal physical weaker exponents identify the canonical weak completion
with a fresh physical anisotropic model. This supplies the norm equality
needed to apply the analytic producer at a second admissible exponent pair. -/

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

namespace Data

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)


variable (loss : m.localization.indices → ℝ) (positive : ∀ i, 0 < loss i)
  (extra : m.localization.indices → Bool → ℝ) (nonnegative : ∀ i b, 0 ≤ extra i b)

include positive nonnegative in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
theorem loweredBounded (i : m.localization.indices) :
    SchwartzAmbientBlocks.SmoothCoreBounded μ m.slope_nonnegative (m.leaves i)
      (ConstructedManifoldLocalization.support m.atlas m.localization i)
      (ConeDyadicSymbols.symbols (m.radial i) (m.angle i))
      (fun b => m.exponent i b - loss i - extra i b) :=
  LocalCompactEmbedding.weak_smoothCoreBounded μ m.slope_nonnegative (m.leaves i)
    (ConstructedManifoldLocalization.support m.atlas m.localization i)
    (m.radial i) (m.angle i) (m.exponent i) (m.boundedBlocks i)
    (positive i) (extra i) (nonnegative i)

def loweredCore := ManifoldPhysicalCore.coreMap m.atlas m.localization m.atlas_mem
  (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
  μ m.slope_nonnegative m.leaves m.radial m.angle
  (fun i b => m.exponent i b - loss i - extra i b)
  (m.loweredBounded loss positive extra nonnegative)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
theorem weak_coordinate_eq_lowered (c : Core (E := E) V) (i : m.localization.indices) :
    ((ManifoldCompactEmbedding.weakCore m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
      positive extra nonnegative c i).val) =
    m.loweredCore loss positive extra nonnegative c i := by
  apply lp.ext
  funext j
  exact ManifoldCompactEmbedding.weak_block m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    positive extra nonnegative c i j

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
set_option maxHeartbeats 800000 in
theorem norm_weakCore_eq_lowered (c : Core (E := E) V) :
    ‖ManifoldCompactEmbedding.weakCore m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
      positive extra nonnegative c‖ = ‖m.loweredCore loss positive extra nonnegative c‖ := by
  have hc (i : m.localization.indices) :
      ‖ManifoldCompactEmbedding.weakCore m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
        μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
        positive extra nonnegative c i‖ = ‖m.loweredCore loss positive extra nonnegative c i‖ :=
    by
      have h := m.weak_coordinate_eq_lowered loss positive extra nonnegative c i
      have hn := congrArg (fun v => ‖v‖) h
      exact hn
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    rw [hc i]
    exact norm_le_pi_norm _ i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    rw [← hc i]
    exact norm_le_pi_norm _ i

/-- An actual isometry of completions, with no new norm-comparison source. -/
def loweredEquivalence :
    ManifoldCompactEmbedding.WeakSpace m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
      positive extra nonnegative ≃ₗᵢ[ℂ]
    closedCore (m.loweredCore loss positive extra nonnegative) :=
  NormCompletionEquivalence.equivalence _ _
    (m.norm_weakCore_eq_lowered loss positive extra nonnegative)

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
