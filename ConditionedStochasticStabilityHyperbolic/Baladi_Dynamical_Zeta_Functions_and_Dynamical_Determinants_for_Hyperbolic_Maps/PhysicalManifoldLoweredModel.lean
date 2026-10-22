module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldWeakening
public import LeanShared.Analysis.DyadicInclusionNorm

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

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
theorem loweredBlockBound (i : m.localization.indices)
    (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support m.atlas m.localization i)) :
    ‖ManifoldPhysicalCore.localBlocks m.atlas m.localization μ m.slope_nonnegative
      m.leaves m.radial m.angle (fun i b => m.exponent i b - loss i - extra i b)
      (m.loweredBounded loss positive extra nonnegative) i f‖ ≤
      m.blockConstant i * ‖m.localCore i f‖ := by
  change ‖LocalCompactEmbedding.weakCoreMap μ m.slope_nonnegative (m.leaves i)
    (ConstructedManifoldLocalization.support m.atlas m.localization i)
    (m.radial i) (m.angle i) (m.exponent i) (m.boundedBlocks i)
    (positive i) (extra i) (nonnegative i) f‖ ≤ _
  rw [LocalCompactEmbedding.weakCoreMap_eq_finalCore]
  exact (DyadicInclusionNorm.norm_exactInclusion_le (m.localBlocks i)
    (loss i) (positive i) (extra i) (nonnegative i)
    (coreLift (m.localBlocks i) f)).trans (m.blockBound i f)

/-- A fresh physical model at the literal weakened exponents, with the same
ordinary functions and actual weighted maps. Its local block bound is proved
by the canonical weakening contraction. -/
@[expose] def loweredModel
    (futureH futureW : m.localization.indices → ℝ)
    (hfutureH : ∀ i, 0 < futureH i) (hfutureW : ∀ i, 0 < futureW i)
    (extraH extraW : m.localization.indices → Bool → ℝ)
    (hextraH : ∀ i b, 0 ≤ extraH i b) (hextraW : ∀ i b, 0 ≤ extraW i b) :
    Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
      (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ :=
  { m with
    exponent := fun i b => m.exponent i b - loss i - extra i b
    boundedBlocks := m.loweredBounded loss positive extra nonnegative
    blockBound := loweredBlockBound m loss positive extra nonnegative
    lossH := futureH
    lossW := futureW
    lossH_positive := hfutureH
    lossW_positive := hfutureW
    extraH := extraH
    extraW := extraW
    extraH_nonnegative := hextraH
    extraW_nonnegative := hextraW }

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
