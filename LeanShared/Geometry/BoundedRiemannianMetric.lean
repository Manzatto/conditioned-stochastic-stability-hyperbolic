module
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-! A bounded auxiliary distance genuinely constructed from a continuous
Riemannian metric. Truncation handles disconnected manifolds, whose length
edistance may be infinite. The original topology is preserved definitionally. -/
public noncomputable section
namespace LeanShared.BoundedRiemannianMetric
open Set Filter Manifold Bundle
open scoped Topology Manifold Bundle ENNReal

@[expose, instance_reducible] def truncate {X : Type*} [EMetricSpace X] : MetricSpace X := by
  let d := fun x y : X => min (edist x y) 1
  have triangle (x y z : X) : d x z ≤ d x y + d y z := by
    by_cases hxy : edist x y ≤ 1
    · by_cases hyz : edist y z ≤ 1
      · exact (min_le_left _ _).trans ((edist_triangle x y z).trans_eq
          (by simp only [d,min_eq_left hxy,min_eq_left hyz]))
      · have lower : 1 ≤ d x y + d y z := by
          dsimp only [d]
          rw [min_eq_right (le_of_not_ge hyz)]
          exact le_add_of_nonneg_left zero_le
        exact (min_le_right _ _).trans lower
    · have lower : 1 ≤ d x y + d y z := by
        dsimp only [d]
        rw [min_eq_right (le_of_not_ge hxy)]
        exact le_add_of_nonneg_right zero_le
      exact (min_le_right _ _).trans lower
  have basis (x : X) : (𝓝 x).HasBasis (fun r : ℝ≥0∞ => 0 < r) (fun r => {y | d x y < r}) := by
    apply Metric.nhds_basis_eball.to_hasBasis
    · intro r hr
      refine ⟨min r 1,lt_min hr (by norm_num),fun y hy => ?_⟩
      change min (edist x y) 1 < min r 1 at hy
      rcases min_lt_iff.mp hy with hy | hy
      · change edist y x < r
        rw [edist_comm]
        exact hy.trans_le (min_le_left _ _)
      · exact False.elim ((not_lt_of_ge (min_le_right r 1)) hy)
    · intro r hr
      refine ⟨r,hr,?_⟩
      intro y hy
      change min (edist x y) 1 < r
      have close : edist x y < r := by
        change edist y x < r at hy
        rwa [edist_comm] at hy
      exact (min_le_left _ _).trans_lt close
  have finite (x y : X) : d x y ≠ ∞ := ne_of_lt
    ((min_le_right (edist x y) 1).trans_lt (by simp))
  letI : PseudoEMetricSpace X := PseudoEMetricSpace.ofEDistOfTopology d
    (fun x => by simp [d]) (fun x y => by simp only [d,edist_comm]) triangle basis
  letI : EMetricSpace X := EMetricSpace.ofT0PseudoEMetricSpace X
  exact EMetricSpace.toMetricSpace finite

theorem truncate_edist {X : Type*} [EMetricSpace X] (x y : X) :
    @edist X (truncate (X := X)).toPseudoMetricSpace.toPseudoEMetricSpace.toEDist x y =
      min (edist x y) 1 := rfl

@[expose, instance_reducible] def metric
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [T3Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) 1 M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] : MetricSpace M :=
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓘(ℝ,E)) M
  truncate

theorem metric_edist
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [T3Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) 1 M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (x y : M) :
    (letI : MetricSpace M := metric (E := E); edist x y) =
      min (Manifold.riemannianEDist (𝓘(ℝ,E)) x y) 1 := rfl

end LeanShared.BoundedRiemannianMetric
