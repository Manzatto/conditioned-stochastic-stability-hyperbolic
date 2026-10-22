module
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanFrames
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
import Mathlib.Tactic.Linarith

/-! Common actual chart-frame bounds in the same Euclidean adapted model. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem ChartAtlas.euclidean_frame_bounds {system : PatchSystem b} (atlas : ChartAtlas system)
    (c : Λ) (hc : c ∈ atlas.centers) (x : Λ) (hx : x ∈ atlas.patch c) :
    let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
      (system.euclideanReferenceFrame c ⟨x,atlas.inside c hx⟩)
    ‖L.toContinuousLinearMap‖ ≤ 2*atlas.bound ∧ ‖L.symm.toContinuousLinearMap‖ ≤ 2*atlas.bound := by
  dsimp only
  rw [system.euclidean_chartFrame c ⟨x,atlas.inside c hx⟩]
  constructor
  · change ‖(ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
      (system.referenceFrame c ⟨x,atlas.inside c hx⟩)).toContinuousLinearMap.comp
      system.euclideanEquiv.symm.toContinuousLinearMap‖ ≤ _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (atlas.frame_bounds c hc x hx).1 system.euclideanEquiv_norm.2
        (norm_nonneg _) (by linarith [atlas.one_le_bound])).trans (by linarith [atlas.one_le_bound]))
  · change ‖system.euclideanEquiv.toContinuousLinearMap.comp
      (ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.referenceFrame c ⟨x,atlas.inside c hx⟩)).symm.toContinuousLinearMap‖ ≤ _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul system.euclideanEquiv_norm.1 (atlas.frame_bounds c hc x hx).2 (norm_nonneg _) (by norm_num))

end LeanShared.HyperbolicAdaptedPatchSystem
