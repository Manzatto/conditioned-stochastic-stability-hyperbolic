module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldLoweredModel
import Mathlib.Tactic.Ring

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

@[expose] def physicalCoreAt
    (t : m.localization.indices → Bool → ℝ)
    (bounded : ∀ i, SchwartzAmbientBlocks.SmoothCoreBounded μ m.slope_nonnegative (m.leaves i)
      (ConstructedManifoldLocalization.support m.atlas m.localization i)
      (ConeDyadicSymbols.symbols (m.radial i) (m.angle i)) (t i)) :=
  ManifoldPhysicalCore.coreMap m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle t bounded

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
private theorem physicalCoreAt_congr
    (t t' : m.localization.indices → Bool → ℝ)
    (bounded : ∀ i, SchwartzAmbientBlocks.SmoothCoreBounded μ m.slope_nonnegative (m.leaves i)
      (ConstructedManifoldLocalization.support m.atlas m.localization i)
      (ConeDyadicSymbols.symbols (m.radial i) (m.angle i)) (t i))
    (bounded' : ∀ i, SchwartzAmbientBlocks.SmoothCoreBounded μ m.slope_nonnegative (m.leaves i)
      (ConstructedManifoldLocalization.support m.atlas m.localization i)
      (ConeDyadicSymbols.symbols (m.radial i) (m.angle i)) (t' i))
    (h : t = t') : m.physicalCoreAt t bounded = m.physicalCoreAt t' bounded' := by
  subst t'
  rfl

variable (a b : m.localization.indices → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
  (ea eb : m.localization.indices → Bool → ℝ)
  (hea : ∀ i j, 0 ≤ ea i j) (heb : ∀ i j, 0 ≤ eb i j)

/-- The intermediate physical model, with a second genuine strict loss. -/
@[expose] def intermediateModel := m.loweredModel a ha ea hea b b hb hb eb eb heb heb

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
set_option maxHeartbeats 800000 in
theorem double_lowering_core :
    (m.intermediateModel a b ha hb ea eb hea heb).loweredCore b hb eb heb =
      m.loweredCore (fun i => a i + b i) (fun i => add_pos (ha i) (hb i))
        (fun i j => ea i j + eb i j) (fun i j => add_nonneg (hea i j) (heb i j)) := by
  apply physicalCoreAt_congr m
  funext i j
  change (m.exponent i j - a i - ea i j) - b i - eb i j = _
  ring

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
