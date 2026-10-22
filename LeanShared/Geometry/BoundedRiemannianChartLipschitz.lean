module
public import LeanShared.Geometry.BoundedRiemannianFunctionLipschitz
public import LeanShared.Geometry.SupportedVectorChartExtension
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic

/-! Actual smooth chart coordinates are locally Lipschitz for the
constructed bounded Riemannian length metric. A compact smooth coordinate
cutoff produces a genuine global vector-valued function, so paths leaving
the chart do not create an unproved local distance comparison. -/
public noncomputable section
namespace LeanShared.BoundedRiemannianMetric
open Set Metric IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle NNReal

theorem chart_local_lipschitz
    {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (x : M) (hx : x ∈ e.source) :
    let _ : MetricSpace M := metric (E := E)
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ e.source ∧
      ∃ L : ℝ≥0, ∀ y ∈ W, ∀ z ∈ W, dist (e y) (e z) ≤ L*dist y z := by
  classical
  obtain ⟨R,hR,sourceR⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hx))
  let φ : ContDiffBump (e x) := ⟨R/4,R/2,by positivity,by linarith⟩
  let h : E → E := fun z => φ z • z
  have compactH : HasCompactSupport h := φ.hasCompactSupport.smul_right
  have supportH : tsupport h ⊆ e.target :=
    (tsupport_smul_subset_left (fun z => φ z) (fun z : E => z)).trans (by
      rw [φ.tsupport_eq]
      exact (closedBall_subset_ball (half_lt_self hR)).trans sourceR)
  let g := SupportedVectorChartExtension.function e h
  have smoothG := SupportedVectorChartExtension.smooth e he h (φ.contDiff.smul contDiff_id) compactH supportH
  let W := e.source ∩ e ⁻¹' ball (e x) φ.rIn
  have openW : IsOpen W := e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
  have inW : x ∈ W := ⟨hx,mem_ball_self φ.rIn_pos⟩
  have agrees z (hz : z ∈ W) : g z = e z := by
    change (if z ∈ e.source then φ (e z) • e z else 0) = e z
    rw [ite_eq_left hz.1,φ.one_of_mem_closedBall (ball_subset_closedBall hz.2),one_smul]
  let _ : MetricSpace M := metric (E := E)
  change ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ e.source ∧ ∃ L : ℝ≥0, _
  obtain ⟨L,lip⟩ := function_exists_lipschitz g (smoothG.of_le (by simp))
  refine ⟨W,openW,inW,inter_subset_left,L,?_⟩
  intro y hy z hz
  simpa only [agrees y hy,agrees z hz] using lip.dist_le_mul y z

end LeanShared.BoundedRiemannianMetric
