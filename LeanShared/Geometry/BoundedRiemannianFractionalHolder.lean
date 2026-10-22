module
public import LeanShared.Geometry.BoundedRiemannianChartLipschitz
public import LeanShared.Geometry.FractionalSubunitRegularity
public import LeanShared.Geometry.FractionalRegularLinearMap
public import LeanShared.Analysis.CompactLocalHolder

/-! Genuine finite fractional chart regularity implies native Holder
regularity for the constructed bounded Riemannian length metric. The order
q may be below one; no C1 regularity is inferred or required. -/
public noncomputable section
namespace LeanShared.BoundedRiemannianMetric
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle

theorem fractional_exists_holder
    {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (f : M → ℂ) {a q : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℂ) q f) :
    let _ : MetricSpace M := metric (E := E)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖f x-f y‖ ≤ C*dist x y^a := by
  have lower := FractionalManifoldRegularity.lower_subunit ha ha1 haq regular
  let _ : MetricSpace M := metric (E := E)
  change ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖f x-f y‖ ≤ C*dist x y^a
  have locally : ∀ x : M, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ V, ∀ z ∈ V, dist (f y) (f z) ≤ C*dist y z^a := by
    intro x
    let e := chartAt E x
    have he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M := chart_mem_maximalAtlas x
    have hx : x ∈ e.source := mem_chart_source E x
    obtain ⟨W,openW,inW,sourceW,L,lip⟩ := chart_local_lipschitz e he x hx
    obtain ⟨U,openU,inU,_,C,hC,bound⟩ := FractionalManifoldRegularity.local_holder_in_chart
      ha ha1 lower e he (e x) (e.map_source hx)
    let V := W ∩ (e.source ∩ e ⁻¹' U)
    have openV : IsOpen V := openW.inter (e.continuousOn.isOpen_inter_preimage e.open_source openU)
    refine ⟨V,openV,⟨inW,hx,inU⟩,C*(L:ℝ)^a,mul_nonneg hC (Real.rpow_nonneg L.coe_nonneg _),?_⟩
    intro y hy z hz
    have actual := bound (e y) hy.2.2 (e z) hz.2.2
    rw [e.left_inv hy.2.1,e.left_inv hz.2.1] at actual
    have coordinates := Real.rpow_le_rpow dist_nonneg (lip y hy.1 z hz.1) ha.le
    rw [Real.mul_rpow L.coe_nonneg dist_nonneg] at coordinates
    have estimate := actual.trans (mul_le_mul_of_nonneg_left
      (by simpa only [dist_eq_norm] using coordinates) hC)
    simpa only [dist_eq_norm,mul_assoc] using estimate
  obtain ⟨C,hC,bound⟩ := CompactLocalHolder.bound_on_compact ha ha1.le isCompact_univ f
    (fun x _ => locally x)
  exact ⟨C,hC,fun x y => by simpa only [dist_eq_norm] using bound x (mem_univ x) y (mem_univ y)⟩


theorem real_fractional_exists_holder
    {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (f : M → ℝ) {a q : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q f) :
    let _ : MetricSpace M := metric (E := E)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, |f x-f y| ≤ C*dist x y^a := by
  have complexRegular := regular.comp_continuousLinearMap Complex.ofRealCLM
  have result := fractional_exists_holder (fun x => (f x : ℂ)) ha ha1 haq complexRegular
  let _ : MetricSpace M := metric (E := E)
  obtain ⟨C,hC,bound⟩ := result
  exact ⟨C,hC,fun x y => by simpa only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using bound x y⟩

end LeanShared.BoundedRiemannianMetric
