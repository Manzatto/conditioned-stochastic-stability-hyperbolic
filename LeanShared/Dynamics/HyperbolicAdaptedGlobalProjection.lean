module
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanProjectionData

/-! The literal global source projector used by the intrinsic full-leaf row:
the actual normalized native field near the reference, stable axis elsewhere.
All pointwise geometric fields are produced, including native-plane identity. -/
@[expose] public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

def PatchSystem.normalizedProjectionPoint (system : PatchSystem b) (c : Λ)
    (x : system.frameDomain c) (z : system.EuclideanModel) : M :=
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val.val x.property.2
    (system.euclideanReferenceFrame c x)
  (chartAt E c.val).symm ((chartAt E c.val) x.val.val+L z)

def PatchSystem.globalNormalizedProjection (system : PatchSystem b) (η : ℝ) (c : Λ)
    (x : system.frameDomain c) (z : system.EuclideanModel) : system.EuclideanModel →L[ℝ] system.EuclideanModel :=
  if dist x.val.val (system.normalizedProjectionPoint c x z)<η then
    system.normalizedProjection c x (system.normalizedProjectionPoint c x z)
  else system.euclideanSecondProjection

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem PatchSystem.global_normalized_projection_data (system : PatchSystem b) (atlas : ChartAtlas system) :
    ∃ η : ℝ, 0<η ∧ ∀ c∈atlas.centers, ∀ x (hx : x∈atlas.patch c),
      let ref : system.frameDomain c := ⟨x,atlas.inside c hx⟩
      (∀ z, ‖system.globalNormalizedProjection η c ref z-system.euclideanSecondProjection‖ ≤ 1/64 ∧
        (∀ v, system.globalNormalizedProjection η c ref z (system.globalNormalizedProjection η c ref z v) =
          system.globalNormalizedProjection η c ref z v) ∧
        Module.finrank ℝ (system.globalNormalizedProjection η c ref z).range = system.framing.stableDimension ∧
        Module.finrank ℝ (system.globalNormalizedProjection η c ref z).ker = system.framing.unstableDimension ∧
        ∀ v∈(system.globalNormalizedProjection η c ref z).ker,
          ‖system.euclideanSecondProjection v‖ ≤ (1/63:ℝ)*‖system.euclideanFirstProjection v‖) ∧
      ∀ z, dist x.val (system.normalizedProjectionPoint c ref z)<η →
        ∃ inside : system.normalizedProjectionPoint c ref z∈(chartAt E c.val).source,
          let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
            (system.euclideanReferenceFrame c ref)
          let A := CenteredTangentJacobianComparison.encoding (chartAt E c.val)
            (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val))
            (system.normalizedProjectionPoint c ref z) inside L
          (system.globalNormalizedProjection η c ref z).ker =
            (b.hyperbolic.normedAdaptedProjection.unstable (system.normalizedProjectionPoint c ref z)).map A.toLinearMap := by
  obtain ⟨η,positiveη,data⟩ := system.normalized_projection_data atlas
  refine ⟨η,positiveη,fun c hc x hx => ?_⟩
  dsimp only
  let ref : system.frameDomain c := ⟨x,atlas.inside c hx⟩
  have axisData := data c hc x hx x.val (by simpa only [dist_self] using positiveη)
  rw [system.normalizedProjection_core c ref] at axisData
  constructor
  · intro z
    by_cases near : dist x.val (system.normalizedProjectionPoint c ref z)<η
    · change ‖system.globalNormalizedProjection η c ref z-system.euclideanSecondProjection‖ ≤ 1/64 ∧ _
      have actual : system.globalNormalizedProjection η c ref z =
          system.normalizedProjection c ref (system.normalizedProjectionPoint c ref z) := by
        unfold PatchSystem.globalNormalizedProjection
        exact ite_eq_left near
      rw [actual]
      exact (data c hc x hx (system.normalizedProjectionPoint c ref z) near).2
    · change ‖system.globalNormalizedProjection η c ref z-system.euclideanSecondProjection‖ ≤ 1/64 ∧ _
      have actual : system.globalNormalizedProjection η c ref z = system.euclideanSecondProjection := by
        unfold PatchSystem.globalNormalizedProjection
        exact ite_eq_right near
      rw [actual]
      exact axisData.2
  · intro z near
    have geometry := data c hc x hx (system.normalizedProjectionPoint c ref z) near
    refine ⟨geometry.1.2,?_⟩
    change (system.globalNormalizedProjection η c ref z).ker = _
    have actual : system.globalNormalizedProjection η c ref z =
        system.normalizedProjection c ref (system.normalizedProjectionPoint c ref z) := by
      unfold PatchSystem.globalNormalizedProjection
      exact ite_eq_left near
    rw [actual]
    exact system.normalizedProjection_ker c ref (system.normalizedProjectionPoint c ref z) geometry.1.2

end LeanShared.HyperbolicAdaptedPatchSystem
