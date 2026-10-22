module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelChartSmoothing
meta import Lean.LibrarySuggestions.Basic

/-! Chart data of the regularized trace family and the partition identity. One generator
step reads a core function only where the weight is nonzero, so a core function equals the
sum of its weighted chart pieces after one step, when the chart weights `wt_j ∘ φ_j · c_j`
sum to one on the image of the weight support. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelTraceCharts"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap
attribute [local instance] Classical.propDecidable
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
  PhysicalModelAnalytic SchwartzJetSpace FiniteRegularTransferRealization

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

/-- Chart cutoffs and test weights of the regularized trace family. -/
structure TraceCharts where
  cut : m.localization.indices → 𝓢(E, ℂ)
  cutCompact : ∀ j, HasCompactSupport (cut j : E → ℂ)
  cutSupport : ∀ j, tsupport (cut j : E → ℂ) ⊆
    ConstructedManifoldLocalization.support m.atlas m.localization j
  cutRegion : ∀ j : m.localization.indices, (m.atlas j).symm '' tsupport (cut j : E → ℂ) ⊆ V
  wt : m.localization.indices → 𝓢(E, ℂ)
  wtCompact : ∀ j, HasCompactSupport (wt j : E → ℂ)
  wtOne : ∀ j, ∀ z ∈ tsupport (wt j : E → ℂ), cut j z = 1

set_option maxHeartbeats 1600000 in
/-- One generator step reads a core function only at images of weight points. -/
theorem generator_congr {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (u u' : Core (E := E) V)
    (same : ∀ x, m.weight x ≠ 0 → SmoothSupportedManifoldCore.functions V u (m.maps a x) =
      SmoothSupportedManifoldCore.functions V u' (m.maps a x)) :
    m.generator a (coreLift m.qa u) = m.generator a (coreLift m.qa u') := by
  rw [generator_core m bound a u, generator_core m bound a u']
  congr 1
  apply m.view_injective
  funext x
  rw [regularAction_apply, regularAction_apply]
  by_cases hx : m.weight x = 0
  · simp [hx]
  · rw [same x hx]

/-- The chart sum of the weighted pieces of a core function. -/
def pieces (tc : TraceCharts m) (v : Core (E := E) V) : Core (E := E) V :=
  ∑ j, extension m j (tc.cut j) (tc.cutCompact j) (tc.cutSupport j) (tc.cutRegion j)
    (weighted m j (tc.cut j) (tc.wt j) (tc.wtOne j) v)

theorem pieces_apply (tc : TraceCharts m) (v : Core (E := E) V) (y : M) :
    SmoothSupportedManifoldCore.functions V (pieces m tc v) y =
      (∑ j : m.localization.indices, if y ∈ (m.atlas j).source then
        tc.wt j (m.atlas j y) * m.localization.cutoff j y else 0) *
        SmoothSupportedManifoldCore.functions V v y := by
  rw [pieces, map_sum, Finset.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (if y ∈ (m.atlas j).source then (weighted m j (tc.cut j) (tc.wt j) (tc.wtOne j) v).val
    (m.atlas j y) else 0) = _
  split_ifs with hy
  · rw [weighted_apply, ConstructedManifoldLocalization.localize_apply _ _ _ _ _ j v y hy]
    ring
  · rw [zero_mul]

/-- After one generator step, a core function is the sum of its weighted chart pieces. -/
theorem partition_decomposition (tc : TraceCharts m) {L : ℝ} (bound : AnalyticBound m L) (a : Ω)
    (partition : ∀ x, m.weight x ≠ 0 → (∑ j : m.localization.indices,
      if m.maps a x ∈ (m.atlas j).source then
        tc.wt j (m.atlas j (m.maps a x)) * m.localization.cutoff j (m.maps a x) else 0) = 1)
    (v : Core (E := E) V) :
    m.generator a (coreLift m.qa v) = m.generator a (coreLift m.qa (pieces m tc v)) :=
  generator_congr m bound a v (pieces m tc v) fun x hx => by
    rw [pieces_apply, partition x hx, one_mul]

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
