module
public import LeanShared.Dynamics.HyperbolicNormedAdaptedProjection
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCones
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! The actual continuous idempotent extension of the invariant splitting,
in the same genuine normalized adapted charts used for the noisy maps. -/
@[expose] public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet HyperbolicAdaptedFramePatches OrthogonalProductCoordinates
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

def PatchSystem.normalizedProjection (system : PatchSystem b) (c : Λ)
    (x : system.frameDomain c) (y : M) : system.EuclideanModel →L[ℝ] system.EuclideanModel :=
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val.val x.property.2
    (system.euclideanReferenceFrame c x)
  L.symm.toContinuousLinearMap.comp
    ((BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E)))
      (trivializationAt E (TangentSpace (𝓘(ℝ,E))) c.val)
      b.hyperbolic.normedAdaptedProjection.projection y).comp L.toContinuousLinearMap)

omit [FiniteDimensional ℝ E] [CompactSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem PatchSystem.referenceFrame_projection (system : PatchSystem b) (c : Λ)
    (x : system.frameDomain c) (z : system.SplitModel) :
    b.hyperbolic.projection x.val.val (system.referenceFrame c x z) =
      system.referenceFrame c x (0,z.2) := by
  let Fu := system.unstableFrame c
  let Fs := system.stableFrame c
  let y : ↥(Λ ∩ (Fu.neighborhood ∩ Fs.neighborhood)) :=
    ⟨x.val.val,x.val.property,x.property.1⟩
  let u := Fu.euclideanCoordinates ⟨y.val,y.property.1,y.property.2.1⟩ z.1
  let s := Fs.euclideanCoordinates ⟨y.val,y.property.1,y.property.2.2⟩ z.2
  change b.hyperbolic.projection y.val (wholeFrame Fu Fs y z) = wholeFrame Fu Fs y (0,z.2)
  rw [wholeFrame_apply,map_add,
    HyperbolicAdaptedContraction.projection_unstable b.hyperbolic y.val y.property.1 u.val u.property,
    HyperbolicAdaptedContraction.projection_stable b.hyperbolic y.val y.property.1 s.val s.property,
    wholeFrame_apply]
  simp only [map_zero,Submodule.coe_zero,zero_add]
  rfl

omit [FiniteDimensional ℝ E] [CompactSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem PatchSystem.euclideanReferenceFrame_projection (system : PatchSystem b) (c : Λ)
    (x : system.frameDomain c) (z : system.EuclideanModel) :
    b.hyperbolic.projection x.val.val (system.euclideanReferenceFrame c x z) =
      system.euclideanReferenceFrame c x (system.euclideanSecondProjection z) := by
  obtain ⟨w,rfl⟩ := system.euclideanEquiv.surjective z
  change b.hyperbolic.projection x.val.val
    (system.referenceFrame c x (system.euclideanEquiv.symm (system.euclideanEquiv w))) =
      system.referenceFrame c x
        (system.euclideanEquiv.symm (secondProjection system.euclideanDimension (system.euclideanEquiv w)))
  have second : secondProjection system.euclideanDimension (system.euclideanEquiv w) =
      system.euclideanEquiv (0,w.2) := secondProjection_apply system.euclideanDimension w
  rw [system.euclideanEquiv.symm_apply_apply,second,system.euclideanEquiv.symm_apply_apply]
  exact system.referenceFrame_projection c x w

theorem PatchSystem.normalizedProjection_core (system : PatchSystem b) (c : Λ)
    (x : system.frameDomain c) :
    system.normalizedProjection c x x.val.val = system.euclideanSecondProjection := by
  let e := trivializationAt E (TangentSpace (𝓘(ℝ,E))) c.val
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val.val x.property.2
    (system.euclideanReferenceFrame c x)
  have inside : x.val.val ∈ e.baseSet := by
    rw [TangentChartTrivialization.baseSet]
    exact x.property.2
  have encoded (v : system.EuclideanModel) :
      L v = e.continuousLinearMapAt ℝ x.val.val (system.euclideanReferenceFrame c x v) := by
    rw [TangentChartTrivialization.forward x.property.2]
    rfl
  apply ContinuousLinearMap.ext
  intro z
  change L.symm (e.continuousLinearMapAt ℝ x.val.val
    (b.hyperbolic.normedAdaptedProjection.projection x.val.val (e.symmL ℝ x.val.val (L z)))) = _
  rw [encoded z,e.symmL_continuousLinearMapAt inside,
    b.hyperbolic.normedAdaptedProjection.core_eq x.val.val x.val.property,
    system.euclideanReferenceFrame_projection,←encoded (system.euclideanSecondProjection z),
    L.symm_apply_apply]

set_option maxHeartbeats 1000000 in
/-- The atlas and the actual projection extension produce the error radius;
no near-projection matrix field is assumed. -/
theorem PatchSystem.normalized_projection_radius (system : PatchSystem b) (atlas : ChartAtlas system)
    {δ : ℝ} (positiveδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ c ∈ atlas.centers, ∀ x (hx : x∈atlas.patch c), ∀ y : M,
      dist x.val y < η → y∈b.hyperbolic.normedAdaptedProjection.collar ∩ (chartAt E c.val).source ∧
      ‖system.normalizedProjection c ⟨x,atlas.inside c hx⟩ y-system.euclideanSecondProjection‖ < δ := by
  classical
  let p := b.hyperbolic.normedAdaptedProjection
  let C : ℝ := 2*atlas.bound
  have positiveC : 0 < C := by dsimp only [C]; linarith [atlas.one_le_bound]
  let ε := δ/(C*C)
  have positiveε : 0 < ε := div_pos positiveδ (mul_pos positiveC positiveC)
  have windows (c : Λ) : ∃ r : ℝ, 0<r ∧ ∀ hc : c∈atlas.centers,
      ∀ x∈atlas.patch c, ∀ y : M, dist x.val y<r →
      y∈p.collar ∩ (chartAt E c.val).source ∧
      ‖BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E)))
        (trivializationAt E (TangentSpace (𝓘(ℝ,E))) c.val) p.projection y-
        BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E)))
        (trivializationAt E (TangentSpace (𝓘(ℝ,E))) c.val) p.projection x.val‖ < ε := by
    by_cases hc : c∈atlas.centers
    · let e := trivializationAt E (TangentSpace (𝓘(ℝ,E))) c.val
      have compact : IsCompact (Subtype.val '' atlas.patch c) := (atlas.compact c).image continuous_subtype_val
      have core : Subtype.val '' atlas.patch c ⊆ Λ := by rintro _ ⟨x,_,rfl⟩; exact x.property
      have chart : Subtype.val '' atlas.patch c ⊆ e.baseSet := by
        rintro _ ⟨x,hx,rfl⟩
        rw [TangentChartTrivialization.baseSet]
        exact (atlas.inside c hx).2
      obtain ⟨r,positiveR,near⟩ := p.exists_ambient_projection_radius e
        (Subtype.val '' atlas.patch c) compact core chart ε positiveε
      refine ⟨r,positiveR,fun _ x hx y hxy => ?_⟩
      have result := near x.val ⟨x,hx,rfl⟩ y hxy
      refine ⟨?_,?_⟩
      · simpa only [e,TangentChartTrivialization.baseSet] using result.1
      · simpa only [BundleEndomorphismCoordinates.coordinates,p.core_eq x.val x.property] using result.2
    · exact ⟨1,by norm_num,fun member => False.elim (hc member)⟩
  choose radii positiveR nearby using windows
  obtain ⟨η,positiveη,common⟩ := CompactUniformCenteredCharts.common_positive atlas.centers radii
    (fun c _ => positiveR c)
  refine ⟨η,positiveη,fun c hc x hx y hxy => ?_⟩
  let e := trivializationAt E (TangentSpace (𝓘(ℝ,E))) c.val
  let A := BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E))) e p.projection
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
    (system.euclideanReferenceFrame c ⟨x,atlas.inside c hx⟩)
  have result := nearby c hc x hx y (hxy.trans_le (common c hc))
  have boundL : ‖L.toContinuousLinearMap‖ ≤ C := by
    rw [show L = system.euclideanEquiv.symm.trans
      (ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.referenceFrame c ⟨x,atlas.inside c hx⟩)) from system.euclidean_chartFrame c _]
    change ‖(ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
      (system.referenceFrame c ⟨x,atlas.inside c hx⟩)).toContinuousLinearMap.comp
        system.euclideanEquiv.symm.toContinuousLinearMap‖ ≤ C
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (atlas.frame_bounds c hc x hx).1 system.euclideanEquiv_norm.2
        (norm_nonneg _) (by linarith [atlas.one_le_bound])).trans (by dsimp only [C]; nlinarith))
  have boundInv : ‖L.symm.toContinuousLinearMap‖ ≤ C := by
    rw [show L = system.euclideanEquiv.symm.trans
      (ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.referenceFrame c ⟨x,atlas.inside c hx⟩)) from system.euclidean_chartFrame c _]
    change ‖system.euclideanEquiv.toContinuousLinearMap.comp
      (ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.referenceFrame c ⟨x,atlas.inside c hx⟩)).symm.toContinuousLinearMap‖ ≤ 2*atlas.bound
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul system.euclideanEquiv_norm.1 (atlas.frame_bounds c hc x hx).2 (norm_nonneg _) (by norm_num))
  refine ⟨result.1,?_⟩
  rw [←system.normalizedProjection_core c ⟨x,atlas.inside c hx⟩]
  have difference : system.normalizedProjection c ⟨x,atlas.inside c hx⟩ y-
      system.normalizedProjection c ⟨x,atlas.inside c hx⟩ x.val =
        L.symm.toContinuousLinearMap.comp ((A y-A x.val).comp L.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [PatchSystem.normalizedProjection,ContinuousLinearMap.comp_apply,sub_apply,map_sub,L,A,e,p]
  rw [difference]
  have estimate : ‖L.symm.toContinuousLinearMap.comp ((A y-A x.val).comp L.toContinuousLinearMap)‖ ≤
      (C*C)*‖A y-A x.val‖ := by
    calc
      _ ≤ ‖L.symm.toContinuousLinearMap‖*(‖A y-A x.val‖*‖L.toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ C*(‖A y-A x.val‖*C) := mul_le_mul boundInv
        (mul_le_mul_of_nonneg_left boundL (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) positiveC.le
      _ = _ := by ring
  calc
    _ ≤ (C*C)*‖A y-A x.val‖ := estimate
    _ < (C*C)*ε := mul_lt_mul_of_pos_left result.2 (mul_pos positiveC positiveC)
    _ = δ := mul_div_cancel₀ δ (ne_of_gt (mul_pos positiveC positiveC))

end LeanShared.HyperbolicAdaptedPatchSystem
