module
public import LeanShared.Geometry.BoundedRiemannianMetric

/-! A two-point inverse-chart estimate for the genuine Riemannian length
edistance. Both endpoints vary in a common coordinate ball. -/
public noncomputable section
namespace LeanShared.BoundedRiemannianMetric
open Set Filter Manifold Metric Bundle MeasureTheory
open scoped Topology Manifold ContDiff Bundle ENNReal NNReal
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
theorem inverse_chart_pair_bound
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) 1 M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (x : M) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ≥0, 0 < C ∧
      ball (extChartAt (𝓘(ℝ,E)) x x) r ⊆ (extChartAt (𝓘(ℝ,E)) x).target ∧
      ∀ y ∈ ball (extChartAt (𝓘(ℝ,E)) x x) r,
      ∀ z ∈ ball (extChartAt (𝓘(ℝ,E)) x x) r,
      riemannianEDist (𝓘(ℝ,E)) ((extChartAt (𝓘(ℝ,E)) x).symm y)
        ((extChartAt (𝓘(ℝ,E)) x).symm z) ≤ C*edist y z := by
  let I := 𝓘(ℝ,E)
  let e := extChartAt I x
  obtain ⟨C,hC,eventual⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt I x
  rw [ModelWithCorners.range_eq_univ,nhdsWithin_univ] at eventual
  have inTarget : e.target ∈ 𝓝 (e x) :=
    (isOpen_extChartAt_target x).mem_nhds (e.map_source (mem_extChartAt_source x))
  obtain ⟨r,hr,safe⟩ := Metric.mem_nhds_iff.mp (inter_mem inTarget eventual)
  refine ⟨r,hr,C,hC,fun y hy => (safe hy).1,?_⟩
  intro y hy z hz
  let η := ContinuousAffineMap.lineMap (R := ℝ) y z
  let γ := e.symm ∘ η
  have segment : Icc 0 1 ⊆ η ⁻¹' ball (e x) r := by
    rw [←image_subset_iff]
    simpa only [η,ContinuousAffineMap.coe_lineMap_eq,←segment_eq_image_lineMap] using
      (convex_ball (e x) r).segment_subset hy hz
  have hη : Icc 0 1 ⊆ η ⁻¹' (e.target ∩
      {q | ‖mfderivWithin I I e.symm (range I) q‖ₑ < C}) := by
    intro t ht
    change η t ∈ e.target ∩ {q | ‖mfderivWithin I I e.symm (range I) q‖ₑ < C}
    simpa only [ModelWithCorners.range_eq_univ,e] using safe (segment ht)
  simp only [preimage_inter,subset_inter_iff] at hη
  have η_smooth : ContMDiffOn (𝓘(ℝ,ℝ)) I 1 η (Icc 0 1) := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have length : riemannianEDist I (e.symm y) (e.symm z) ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  apply length.trans
  rw [←lintegral_fderiv_lineMap_eq_edist,pathELength_eq_lintegral_mfderivWithin_Icc,
    ←lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have derivative : mfderivWithin (𝓘(ℝ,ℝ)) I γ (Icc 0 1) t =
      (mfderivWithin I I e.symm (range I) (η t)).comp
        (mfderivWithin (𝓘(ℝ,ℝ)) I η (Icc 0 1) t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have evaluated : mfderivWithin (𝓘(ℝ,ℝ)) I γ (Icc 0 1) t 1 =
      (mfderivWithin I I e.symm (range I) (η t))
        (mfderivWithin (𝓘(ℝ,ℝ)) I η (Icc 0 1) t 1) := congr($derivative 1)
  rw [evaluated]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [I,η,mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

end LeanShared.BoundedRiemannianMetric
