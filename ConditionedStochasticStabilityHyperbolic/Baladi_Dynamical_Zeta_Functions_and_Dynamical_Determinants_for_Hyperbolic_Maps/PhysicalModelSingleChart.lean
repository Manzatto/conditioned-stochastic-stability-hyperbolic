module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnalytic
public import LeanShared.Geometry.SingleChartTransfer

/-! One generator step on a function living in a single chart: if a core function is the
zero extension of a local function `f` in chart `j`, the chart-pair estimate of the letter
bounds the strong norm of its image by the local block norm of `f` alone. -/
@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff
attribute [local instance] Classical.propDecidable
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelSingleChart
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
  PhysicalModelPairBounds PhysicalModelAnalytic FiniteRegularTransferRealization

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

set_option maxHeartbeats 1600000 in
theorem single_chart {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (strong : ℝ)
    (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
    (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
    (j : m.localization.indices)
    (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support m.atlas m.localization j))
    (c : Core (E := E) V)
    (hc : ∀ x, SmoothSupportedManifoldCore.functions V c x =
      if x ∈ (m.atlas j).source then f.val (m.atlas j x) else 0) :
    ‖m.generator a (coreLift m.qa c)‖ ≤
      (strong + ∑ i, remainder i j) * ‖m.localBlocks j f‖ := by
  have sumR : 0 ≤ ∑ i, remainder i j := Finset.sum_nonneg fun i _ => hR i j
  rw [generator_core m bound a c, regularAction_eq m a c]
  refine SingleChartTransfer.realization_single_norm m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) m.view
    m.regularCore m.regularCore_dense m.view_core m.evaluate m.evaluation m.localView
    m.localView_injective m.localCore m.localCore_dense m.localView_core m.localEvaluate
    m.localEvaluation m.coordinateConstant m.coordinateBound m.localBlocks m.blockConstant
    m.blockBound m.view_injective (m.maps a) m.weight (m.coreRegular a) estimate.pairMember
    j f c hc _ (mul_nonneg (add_nonneg hs sumR) (norm_nonneg _)) fun i => ?_
  refine (estimate.bound i j f).trans ?_
  have weak := weak_le m j f
  have single : remainder i j ≤ ∑ k, remainder k j :=
    Finset.single_le_sum (f := fun k => remainder k j) (fun k _ => hR k j) (Finset.mem_univ i)
  calc strong * ‖m.localBlocks j f‖ + remainder i j * ‖m.weakLocalBlocksW j f‖
      ≤ strong * ‖m.localBlocks j f‖ + (∑ k, remainder k j) * ‖m.localBlocks j f‖ :=
        add_le_add le_rfl (mul_le_mul single weak (norm_nonneg _) sumR)
    _ = (strong + ∑ k, remainder k j) * ‖m.localBlocks j f‖ := by ring

end ConditionedStochasticStabilityHyperbolic.PhysicalModelSingleChart
