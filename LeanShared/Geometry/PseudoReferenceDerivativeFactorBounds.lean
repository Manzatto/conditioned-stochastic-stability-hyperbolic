module
public import LeanShared.Geometry.PseudoReferenceCompactPatches
public import LeanShared.Geometry.CompactRiemannianMFDeriv
public import LeanShared.Geometry.CompactRiemannianChartBounds
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! A uniform bound for the ACTUAL native derivative factor appearing in the
misaligned centered derivative. Compact target tubes and native Riemannian
differential bounds are constructed from the literal map. -/
public noncomputable section
namespace LeanShared.PseudoReferenceCoordinateMaps
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle

set_option maxHeartbeats 1600000 in
theorem exists_derivative_factor_bound
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} {B : ℝ} {h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ}
    (d : HyperbolicBasicSet.PseudoReferenceGeometry h)
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (positiveB : 0 < B) (bounds : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B)
    (H : M → M) (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 H) :
    ∃ C : ℝ, 0 < C ∧ ∃ η : ℝ, 0 < η ∧ ∀ x y : Λ, dist (H x.val) y.val < η →
      H x.val ∈ (chart d y).source ∧
      let e := trivializationAt E (fun z : M => TangentSpace (𝓘(ℝ, E)) z) (d.index y).val
      ‖(e.continuousLinearMapAt ℝ (H x.val)).comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (frame x).toContinuousLinearMap)‖ ≤ C := by
  obtain ⟨D,positiveD,derivative⟩ := CompactRiemannianMFDeriv.exists_norm_bound H smooth Λ h.compact
  have tubes (i : Λ) := (compact_ambientPatch d i).exists_cthickening_subset_open
    (chartAt E i.val).open_source (ambientPatch_source d i)
  choose ρ positiveρ tubeInside using tubes
  let targetTube (i : Λ) := Metric.cthickening (ρ i) (ambientPatch d i)
  have compactTube (i : Λ) : IsCompact (targetTube i) := (compact_ambientPatch d i).cthickening
  have forward (i : Λ) := CompactRiemannianChartBounds.forward (chartAt E i.val)
    (chart_mem_maximalAtlas i.val) (targetTube i) (compactTube i) (tubeInside i)
  choose F positiveF boundF using forward
  let total := ∑ i ∈ d.centers, F i
  have nonnegativeTotal : 0 ≤ total := Finset.sum_nonneg (fun i _ => (positiveF i).le)
  have each (i : Λ) (hi : i ∈ d.centers) : F i ≤ total :=
    Finset.single_le_sum (fun j _ => (positiveF j).le) hi
  obtain ⟨η,positiveη,common⟩ := CompactUniformCenteredCharts.common_positive d.centers ρ
    (fun i _ => positiveρ i)
  refine ⟨1 + total * D * B,by positivity,η,positiveη,fun x y near => ?_⟩
  have targetMember : H x.val ∈ targetTube (d.index y) :=
    Metric.mem_cthickening_of_dist_le _ y.val (ρ (d.index y)) (ambientPatch d (d.index y))
      (selected_ambientPatch d y) (near.le.trans (common (d.index y) (d.index_mem y)))
  have target := tubeInside (d.index y) targetMember
  refine ⟨target,?_⟩
  have chartBound : ‖(trivializationAt E (fun z : M => TangentSpace (𝓘(ℝ, E)) z)
      (d.index y).val).continuousLinearMapAt ℝ (H x.val)‖ ≤ F (d.index y) := by
    rw [TangentChartTrivialization.forward target]
    exact boundF (d.index y) (H x.val) targetMember
  calc
    _ ≤ ‖(trivializationAt E (fun z : M => TangentSpace (𝓘(ℝ, E)) z)
        (d.index y).val).continuousLinearMapAt ℝ (H x.val)‖ *
        ‖(mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (frame x).toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ F (d.index y) * (D * B) := by
      apply mul_le_mul chartBound
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (derivative x.val x.property) (bounds x) (norm_nonneg (frame x).toContinuousLinearMap) positiveD.le)
      · exact norm_nonneg ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (frame x).toContinuousLinearMap)
      · exact (positiveF _).le
    _ ≤ total * (D * B) := mul_le_mul_of_nonneg_right (each (d.index y) (d.index_mem y)) (by positivity)
    _ ≤ 1 + total * D * B := by nlinarith

end LeanShared.PseudoReferenceCoordinateMaps
