module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseReferenceJacobianHolder
public import LeanShared.Geometry.BoundedRiemannianChartLipschitz
public import LeanShared.Analysis.CompactUniformWindowHolder

/-! Actual ORIGINAL inverse Jacobians have one global Holder bound for the
constructed bounded Riemannian length metric. Compactness chooses the noise
window before ALL controls; no continuity in noise scale is assumed. -/
public noncomputable section
set_option maxHeartbeats 3200000
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle MeasureTheory Measure Metric
open scoped Topology Manifold ContDiff Bundle NNReal

theorem InverseFamily.referenceJacobian_global_holder
    {E M ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {r a : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (s : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (ha : 0 < a) (ha1 : a < 1) (lower : a+1 < r)
    (regular : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) :
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ J.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ (ε : ℝ≥0) (hp : 0 < ε) (_hw : ε ≤ η) (hwJ : ε ≤ J.window) (control : cube (ι := ι) ε),
      (∀ x, |s.jacobian (J.homeomorph ε hp hwJ control) x| ≤ B) ∧
      ∀ x y, |s.jacobian (J.homeomorph ε hp hwJ control) x-
        s.jacobian (J.homeomorph ε hp hwJ control) y| ≤
          C*(let _ : MetricSpace M := LeanShared.BoundedRiemannianMetric.metric (E := E); dist x y)^a := by
  classical
  let originalWindow := J.window
  have originalPositive := J.positive
  let P := Σ ε : {ε : ℝ≥0 // 0 < ε ∧ ε ≤ J.window}, cube (ι := ι) ε.val
  let family : P → M ≃ₜ M := fun p => J.homeomorph p.1.val p.1.property.1 p.1.property.2 p.2
  let f : P → M → ℝ := fun p x => s.jacobian (family p) x
  have coordinateControls := fun x : M => J.referenceJacobian_local_controls s μ ha ha1 lower regular inverse
    (chartAt E (T.symm x)) (chartAt E x) (chart_mem_maximalAtlas _) (chart_mem_maximalAtlas _)
    ((chartAt E x) x) ((chartAt E x).map_source (mem_chart_source E x))
    (by rw [(chartAt E x).left_inv (mem_chart_source E x)]; exact mem_chart_source E (T.symm x))
  let _ : MetricSpace M := LeanShared.BoundedRiemannianMetric.metric (E := E)
  have localBound : ∀ x : M, ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
      ∃ η : ℝ≥0, 0 < η ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ p : P, p.1.val ≤ η →
        (∀ y ∈ W, ‖f p y‖ ≤ B) ∧
        ∀ y ∈ W, ∀ z ∈ W, ‖f p y-f p z‖ ≤ C*dist y z^a := by
    intro x
    obtain ⟨δ,hδ,η,window,hη,B,C,hB,hC,controls⟩ := coordinateControls x
    let d := chartAt E x
    obtain ⟨W,openW,inW,insideW,L,lip⟩ := LeanShared.BoundedRiemannianMetric.chart_local_lipschitz d
      (chart_mem_maximalAtlas x) x (mem_chart_source E x)
    let V := W ∩ (d.source ∩ d ⁻¹' ball (d x) δ)
    have openV : IsOpen V := openW.inter (d.continuousOn.isOpen_inter_preimage d.open_source isOpen_ball)
    have inV : x ∈ V := ⟨inW,mem_chart_source E x,mem_ball_self hδ⟩
    have coordinate (y : M) (hy : y ∈ V) : d y ∈ closedBall (d x) δ := ball_subset_closedBall hy.2.2
    refine ⟨V,openV,inV,η,hη,B,C*(L:ℝ)^a,hB,mul_nonneg hC (Real.rpow_nonneg L.coe_nonneg _),?_⟩
    intro p hp
    have actual := controls p.1.val p.1.property.1 hp p.2
    refine ⟨?_,?_⟩
    · intro y hy
      have value := (actual (d y) (coordinate y hy)).1
      rw [d.left_inv hy.2.1] at value
      simpa only [Real.norm_eq_abs] using value
    · intro y hy z hz
      have increment := (actual (d y) (coordinate y hy)).2 (d z) (coordinate z hz)
      rw [d.left_inv hy.2.1,d.left_inv hz.2.1] at increment
      have difference := Real.rpow_le_rpow dist_nonneg (lip y hy.1 z hz.1) ha.le
      rw [Real.mul_rpow L.coe_nonneg dist_nonneg] at difference
      have estimate := increment.trans (mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using difference) hC)
      simpa only [Real.norm_eq_abs,mul_assoc] using estimate
  obtain ⟨η,hη,B,C,hB,hC,global⟩ := LeanShared.CompactUniformLocalHolder.window_bounds f
    (fun p : P => p.1.val) a ha.le localBound
  refine ⟨min η originalWindow,lt_min hη originalPositive,min_le_right _ _,B,C,hB,hC,?_⟩
  intro ε hp hw hwJ control
  have actual := global (⟨⟨ε,hp,hwJ⟩,control⟩ : P) (hw.trans (min_le_left _ _))
  simpa only [Real.norm_eq_abs] using actual

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
