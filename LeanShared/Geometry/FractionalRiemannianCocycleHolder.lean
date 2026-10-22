module

public import LeanShared.Geometry.FractionalChartOneJet
public import LeanShared.Geometry.NativeChartCocycleDerivative
public import LeanShared.Geometry.BoundedRiemannianChartLipschitz
public import LeanShared.Analysis.CompactLocalHolder

/-! Actual C^(1+a) manifold maps have uniformly Hölder native coordinate
cocycles on every compact valid fixed-chart patch, in the CONSTRUCTED
bounded Riemannian length metric. The chart Lipschitz and derivative
Hölder constants are derived, not supplied. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

set_option maxHeartbeats 2400000 in
theorem Regular.compact_native_cocycle_holder {a : ℝ} (positive : 0 < a) (small : a < 1)
    {f : M → M} (regular : Regular (E := E) (F := E) (a + 1) f)
    (source target : M) (K : Set M) (compact : IsCompact K)
    (inside : K ⊆ (chartAt E source).source) (image : MapsTo f K (chartAt E target).source) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    ∃ C ≥ 0, ∀ x ∈ K, ∀ y ∈ K,
      ‖BundleProjectionCocycleCoordinates.map (TangentSpace (𝓘(ℝ,E)))
          (trivializationAt E (TangentSpace (𝓘(ℝ,E))) source)
          (trivializationAt E (TangentSpace (𝓘(ℝ,E))) target) x (f x)
          (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x) -
        BundleProjectionCocycleCoordinates.map (TangentSpace (𝓘(ℝ,E)))
          (trivializationAt E (TangentSpace (𝓘(ℝ,E))) source)
          (trivializationAt E (TangentSpace (𝓘(ℝ,E))) target) y (f y)
          (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f y)‖ ≤ C * dist x y ^ a := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  dsimp only
  let c := chartAt E source
  let d := chartAt E target
  let A := fun x : M => fderiv ℝ (d ∘ f ∘ c.symm) (c x)
  have floor : ⌊a + 1⌋₊ = 1 := by rw [Nat.floor_add_one positive.le, Nat.floor_eq_zero.mpr small]
  have smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 f := by
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
  refine ⟨C, nonnegativeC, fun x hx y hy => ?_⟩
  rw [← NativeChartCocycleDerivative.fderiv_eq f (smooth.mdifferentiable one_ne_zero)
      source target x (inside hx) (image hx),
    ← NativeChartCocycleDerivative.fderiv_eq f (smooth.mdifferentiable one_ne_zero)
      source target y (inside hy) (image hy)]
  simpa only [A, c, d, dist_eq_norm] using bound x hx y hy

end LeanShared.FractionalManifoldRegularity
