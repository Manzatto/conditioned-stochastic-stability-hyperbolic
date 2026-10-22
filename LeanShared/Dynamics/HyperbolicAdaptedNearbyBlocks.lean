module
public import LeanShared.Dynamics.HyperbolicAdaptedFrameBlocks
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas

/-! Nearby target references stay in the genuine adapted target patch.
Their relative chart-frame error is uniformly small, and the true one-step
derivative has the exact contracting diagonal blocks in that same patch. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem ChartAtlas.near_image_blocks {system : PatchSystem b} (atlas : ChartAtlas system)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ η > 0, ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      dist (T x.val) y.val < η → ∃ ht : forwardPoint b x ∈ system.frameDomain d,
      let e := system.referenceFrame c ⟨x, atlas.inside c hx⟩
      let f := system.referenceFrame d ⟨forwardPoint b x, ht⟩
      ∃ S : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ]
          EuclideanSpace ℝ (Fin system.framing.stableDimension),
      ∃ U : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ]
          EuclideanSpace ℝ (Fin system.framing.unstableDimension),
        ‖S.toContinuousLinearMap‖ ≤ system.rate ∧ ‖U.symm.toContinuousLinearMap‖ ≤ system.rate ∧
        f.symm.toContinuousLinearMap.comp
          ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x.val).comp e.toContinuousLinearMap) =
            U.toContinuousLinearMap.prodMap S.toContinuousLinearMap ∧
        ‖(ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
            (system.referenceFrame d ⟨y, atlas.inside d hy⟩)).symm.toContinuousLinearMap.comp
          (ContinuousCenteredFrameCharts.chartFrame d.val (T x.val) ht.2 f).toContinuousLinearMap -
            ContinuousLinearMap.id ℝ _‖ < δ := by
  obtain ⟨η, positiveη, near⟩ := system.relative_reference_radii atlas.centers atlas.patch
    atlas.compact atlas.inside δ positiveδ
  refine ⟨η, positiveη, ?_⟩
  intro c _hc d hd x hx y hy small
  have small' : dist y (forwardPoint b x) < η := by
    simpa only [Subtype.dist_eq, forwardPoint, dist_comm] using small
  obtain ⟨ht, close⟩ := near d hd y hy (forwardPoint b x) small'
  obtain ⟨S, U, boundS, boundU, diagonal⟩ := system.actual_frame_blocks
    forward backward c d x (atlas.inside c hx) ht
  exact ⟨ht, S, U, boundS, boundU, diagonal, close⟩

end LeanShared.HyperbolicAdaptedPatchSystem
