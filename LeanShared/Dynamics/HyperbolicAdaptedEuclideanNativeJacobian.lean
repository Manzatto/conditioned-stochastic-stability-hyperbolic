module
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanEndpointTubes
public import LeanShared.Geometry.CompactNormalizedChartTube
public import LeanShared.Geometry.CenteredCompactChartEncodingBounds
import all LeanShared.Geometry.CompactUniformCenteredCharts
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
import Mathlib.Tactic.Linarith

/-! Common actual chart-frame bounds in the same Euclidean adapted model. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem ChartAtlas.euclidean_native_jacobian_bound {system : PatchSystem b} (atlas : ChartAtlas system) :
    ∃ radius > 0, ∃ C > 0,
      ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.euclideanReferenceFrame c ⟨x,atlas.inside c hx⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.euclideanReferenceFrame d ⟨y,atlas.inside d hy⟩)
      ∀ z w : system.EuclideanModel, ‖z‖ ≤ radius → ‖w‖ ≤ radius →
      let p := (chartAt E c.val).symm ((chartAt E c.val) x.val+L z)
      let q := (chartAt E d.val).symm ((chartAt E d.val) y.val+R w)
      ∀ H : M → M, H p = q →
      MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) H p →
      ∀ D : TangentSpace (𝓘(ℝ,E)) p ≃L[ℝ] TangentSpace (𝓘(ℝ,E)) (H p),
      D.toContinuousLinearMap = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H p →
      ∀ U : Submodule ℝ (TangentSpace (𝓘(ℝ,E)) p), ∀ global : system.EuclideanModel → system.EuclideanModel,
      global =ᶠ[_root_.nhds z] CenteredManifoldCoordinates.centered L R
        ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
        (chartAt E d.val ∘ H ∘ (chartAt E c.val).symm) →
      ∃ hp : p ∈ (chartAt E c.val).source,
        (D.toLinearMap.domRestrict U).normDet ≤
          (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) C *
            GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) C) *
          ((fderiv ℝ global z).toLinearMap.domRestrict
            ((CenteredTangentJacobianComparison.encoding (chartAt E c.val)
              (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val)) p hp L).toContinuousLinearMap.comp
                U.subtypeL).toLinearMap.range).normDet := by
  obtain ⟨radius,positiveRadius,C,positiveC,K,compactK,estimates⟩ := atlas.euclidean_endpoint_tubes
  refine ⟨radius,positiveRadius,C,positiveC,?_⟩
  intro c hc d hd x hx y hy
  dsimp only
  intro z w smallZ smallW H image smooth D differential U global agreement
  have sourceFacts := estimates c hc x hx z smallZ
  have targetFacts := estimates d hd y hy w smallW
  obtain ⟨hp,sourceNorm,_sourceInvNorm⟩ := sourceFacts.2.2
  obtain ⟨hq,_targetNorm,targetInvNorm⟩ := targetFacts.2.2
  have hpTarget : H ((chartAt E c.val).symm ((chartAt E c.val) x.val+
      ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.euclideanReferenceFrame c ⟨x,atlas.inside c hx⟩) z)) ∈ (chartAt E d.val).source := by
    rw [image]
    exact hq
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
    (system.euclideanReferenceFrame c ⟨x,atlas.inside c hx⟩)
  let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
    (system.euclideanReferenceFrame d ⟨y,atlas.inside d hy⟩)
  let p := (chartAt E c.val).symm ((chartAt E c.val) x.val+L z)
  have inverseNorm : ‖(CenteredTangentJacobianComparison.encoding (chartAt E d.val)
      (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas d.val)) (H p) hpTarget R).symm.toContinuousLinearMap‖ ≤ C := by
    have pointEq : (⟨H p,hpTarget⟩ : (chartAt E d.val).source) =
        ⟨(chartAt E d.val).symm ((chartAt E d.val) y.val+R w),hq⟩ := Subtype.ext image
    have normEq := congrArg (fun a : (chartAt E d.val).source =>
      ‖(CenteredTangentJacobianComparison.encoding (chartAt E d.val)
        (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas d.val)) a.val a.property R).symm.toContinuousLinearMap‖) pointEq
    exact normEq.le.trans targetInvNorm
  have coordinate : L.symm ((chartAt E c.val) p-(chartAt E c.val) x.val) = z := by
    dsimp only [p]
    rw [(chartAt E c.val).right_inv sourceFacts.1,add_sub_cancel_left,L.symm_apply_apply]
  have actual := CenteredTangentJacobianComparison.native_jacobian_le_of_eventuallyEq H p
    (chartAt E c.val) (chartAt E d.val)
    (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val))
    (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas d.val))
    hp hpTarget L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val) smooth D differential U global
    (by simpa only [coordinate] using agreement) C C positiveC.le positiveC.le
    (fun v => (ContinuousLinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right sourceNorm (norm_nonneg v)))
    (fun v => (ContinuousLinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right inverseNorm (norm_nonneg v)))
  refine ⟨hp,?_⟩
  simpa only [coordinate] using actual

end LeanShared.HyperbolicAdaptedPatchSystem
