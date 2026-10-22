module
public import LeanShared.Geometry.FiniteSmoothReferenceLocalDensity
public import LeanShared.MeasureTheory.FiniteChartDensity
public import LeanShared.MeasureTheory.CoordinatePatchHomeomorph

/-! Actual local densities of the pushforward reference under a genuine C1
diffeomorphism, computed by transporting its weighted coordinate charts. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff ENNReal

@[expose] def Data.transportedChart
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (_d : Data (E := E) (M := M)) (H : M ≃ₜ M) (x : M) : OpenPartialHomeomorph M E :=
  H.symm.transOpenPartialHomeomorph (chartAt E x)

@[expose] def Data.pushforwardDensity
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (d : Data (E := E) (M := M)) (H : M ≃ₜ M) (c : OpenPartialHomeomorph M E) : E → ℝ :=
  FiniteChartDensity.density d.index (d.transportedChart H) d.density c

private theorem transported_regular
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (H : M ≃ₜ M)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H.symm)
    (x : M) (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    ContDiffOn ℝ 1 ((d.transportedChart H x).symm.trans c).symm
      ((d.transportedChart H x).symm.trans c).target := by
  intro y hy
  have first : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 c.symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) hc hy.1).of_le (by decide)
  have middle := inverse.contMDiffAt.comp y first
  have last : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (chartAt E x) (H.symm (c.symm y)) :=
    (contMDiffAt_of_mem_maximalAtlas (n := ∞) (chart_mem_maximalAtlas x) hy.2).of_le (by decide)
  exact (last.comp y middle).contDiffAt.contDiffWithinAt

theorem Data.pushforwardDensity_continuousOn
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (H : M ≃ₜ M)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H.symm)
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    ContinuousOn (d.pushforwardDensity H c) c.target := by
  apply continuousOn_finsetSum
  intro x _
  exact CoordinateJacobianDensity.continuousOn _ _ _ (transported_regular d H inverse x c hc)
    (d.smooth x).continuous (d.compact_support x) (d.support x)

theorem Data.pushforwardDensity_positive
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (H : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) H)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) H.symm)
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (y : E) (inside : y ∈ c.target) : 0 < d.pushforwardDensity H c y := by
  classical
  obtain ⟨x,member,source,positive⟩ := d.cover (H.symm (c.symm y))
  have chartC : c.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
  have xSmooth : chartAt E x ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M := chart_mem_maximalAtlas x
  have chartX : (chartAt E x).MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas xSmooth).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas xSmooth).mdifferentiableOn (by simp)⟩
  obtain ⟨L,derivative⟩ := DiffeomorphismChartDerivative.exists_equivalence H.symm inverse forward
    c (chartAt E x) chartC chartX (c.symm y) (c.map_target inside) source
  have actual : HasFDerivAt ((d.transportedChart H x).symm.trans c).symm L.toContinuousLinearMap y := by
    rw [OpenPartialHomeomorph.coe_trans_symm,OpenPartialHomeomorph.symm_symm]
    simpa only [Data.transportedChart,Homeomorph.transOpenPartialHomeomorph_apply,Function.comp_def,
      c.right_inv inside] using derivative
  have term : 0 < CoordinateJacobianDensity.density (d.transportedChart H x) c (d.density x) y := by
    change 0 < if y ∈ ((d.transportedChart H x).symm.trans c).target then _ else _
    rw [ite_eq_left (show y ∈ ((d.transportedChart H x).symm.trans c).target from ⟨inside,source⟩),actual.fderiv]
    exact mul_pos (abs_pos.mpr L.toLinearEquiv.isUnit_det'.ne_zero) positive
  exact term.trans_le (Finset.single_le_sum (fun i _ =>
    CoordinateJacobianDensity.nonnegative _ _ _ (fun z => (d.bounds i z).1) y) member)

set_option maxHeartbeats 1600000 in
theorem Data.pushforward_local_measure
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (H : M ≃ₜ M) (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H.symm)
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    (((d.measure μ).map H).restrict c.source).map c =
      (μ.restrict c.target).withDensity (fun y => ENNReal.ofReal (d.pushforwardDensity H c y)) := by
  have transported : (d.measure μ).map H =
      FiniteChartDensity.measure d.index (d.transportedChart H) d.density μ := by
    unfold Data.measure
    rw [Measure.map_finset_sum H.continuous.measurable.aemeasurable]
    exact Finset.sum_congr rfl (fun x _ => CoordinatePatchMeasure.map_homeomorph H _ _ _)
  rw [transported]
  exact FiniteChartDensity.local_measure _ _ _ _ _
    (fun x _ => transported_regular d H inverse x c hc) (fun x _ => (d.smooth x).continuous)
    (fun x _ => d.compact_support x) (fun x _ => d.support x) (fun x _ y => (d.bounds x y).1)

end LeanShared.FiniteSmoothReferenceCharts
