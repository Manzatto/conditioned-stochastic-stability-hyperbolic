module

public import LeanShared.Geometry.FractionalChartOneJet
public import LeanShared.Geometry.BoundedRiemannianChartLipschitz
public import LeanShared.Analysis.CompactLocalHolder

/-! Actual coordinate derivatives of C^(1+a) maps into arbitrary manifolds
are Hölder on compact valid source patches for the constructed length
metric. Target and source chart dimensions may differ. All chart
Lipschitz and local derivative Hölder constants are derived. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E F M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ,F)) ∞ N]
  [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

set_option maxHeartbeats 2400000 in
theorem Regular.compact_coordinate_derivative_holder {a : ℝ} (positive : 0 < a) (small : a < 1)
    {f : M → N} (regular : Regular (E := E) (F := F) (a + 1) f)
    (source : M) (target : N) (K : Set M) (compact : IsCompact K)
    (inside : K ⊆ (chartAt E source).source) (image : MapsTo f K (chartAt F target).source) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    ∃ C ≥ 0, ∀ x ∈ K, ∀ y ∈ K,
      ‖fderiv ℝ ((chartAt F target) ∘ f ∘ (chartAt E source).symm) (chartAt E source x) -
        fderiv ℝ ((chartAt F target) ∘ f ∘ (chartAt E source).symm) (chartAt E source y)‖ ≤ C * dist x y ^ a := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  dsimp only
  let c := chartAt E source
  let d := chartAt F target
  let A := fun x : M => fderiv ℝ (d ∘ f ∘ c.symm) (c x)
  have floor : ⌊a + 1⌋₊ = 1 := by rw [Nat.floor_add_one positive.le, Nat.floor_eq_zero.mpr small]
  have smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f := by
    simpa only [floor, Nat.cast_one] using regular.differentiable
  have localBound (x : M) (hx : x ∈ K) : ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ W, ∀ z ∈ W,
        dist (A y) (A z) ≤ C * dist y z ^ a := by
    have jet := regular.one_jet_in_charts positive small c d
      (chart_mem_maximalAtlas source) (chart_mem_maximalAtlas target)
      (c x) (c.map_source (inside hx)) (by simpa only [c.left_inv (inside hx)] using image hx)
    obtain ⟨U, openU, memberU, C, nonnegativeC, holder⟩ := jet.2
    obtain ⟨W, openW, memberW, _, L, lipschitz⟩ := BoundedRiemannianMetric.chart_local_lipschitz
      c (chart_mem_maximalAtlas source) x (inside hx)
    let V := W ∩ (c.source ∩ c ⁻¹' U)
    have openV : IsOpen V := openW.inter (c.continuousOn.isOpen_inter_preimage c.open_source openU)
    refine ⟨V, openV, ⟨memberW, inside hx, memberU⟩, C * (L : ℝ) ^ a,
      mul_nonneg nonnegativeC (Real.rpow_nonneg L.coe_nonneg _), ?_⟩
    intro y hy z hz
    have bound := holder (c y) hy.2.2 (c z) hz.2.2
    have lip := lipschitz y hy.1 z hz.1
    have powers := Real.rpow_le_rpow dist_nonneg lip positive.le
    rw [Real.mul_rpow L.coe_nonneg dist_nonneg] at powers
    rw [dist_eq_norm]
    have weighted := mul_le_mul_of_nonneg_left powers nonnegativeC
    rw [dist_eq_norm] at weighted
    simpa only [A, mul_assoc] using bound.trans weighted
  obtain ⟨C, nonnegativeC, bound⟩ := CompactLocalHolder.bound_on_compact positive small.le compact A localBound
  exact ⟨C, nonnegativeC, fun x hx y hy => by simpa only [A, c, d, dist_eq_norm] using bound x hx y hy⟩

end LeanShared.FractionalManifoldRegularity
