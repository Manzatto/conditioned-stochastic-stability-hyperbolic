module

public import LeanShared.Geometry.FractionalRiemannianCocycleHolder

/-! One actual Hölder constant controls all valid native source/target
pairs in a finite compact chart family. Compact chart-pair domains and
their cocycle estimates are constructed internally from C^(1+a). -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle BigOperators
namespace LeanShared.FractionalManifoldRegularity
variable {E M I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype I]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

set_option maxHeartbeats 1600000 in
theorem Regular.finite_native_cocycle_holder {a : ℝ} (positive : 0 < a) (small : a < 1)
    {f : M → M} (regular : Regular (E := E) (F := E) (a + 1) f)
    (centers : I → M) (patch : I → Set M) (compact : ∀ i, IsCompact (patch i))
    (inside : ∀ i, patch i ⊆ (chartAt E (centers i)).source) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    ∃ C ≥ 0, ∀ i j : I, ∀ x ∈ patch i, ∀ y ∈ patch i,
      f x ∈ patch j → f y ∈ patch j →
      ‖BundleProjectionCocycleCoordinates.map (TangentSpace (𝓘(ℝ,E)))
          (trivializationAt E (TangentSpace (𝓘(ℝ,E))) (centers i))
          (trivializationAt E (TangentSpace (𝓘(ℝ,E))) (centers j)) x (f x)
          (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x) -
        BundleProjectionCocycleCoordinates.map (TangentSpace (𝓘(ℝ,E)))
          (trivializationAt E (TangentSpace (𝓘(ℝ,E))) (centers i))
          (trivializationAt E (TangentSpace (𝓘(ℝ,E))) (centers j)) y (f y)
          (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f y)‖ ≤ C * dist x y ^ a := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  dsimp only
  have floor : ⌊a + 1⌋₊ = 1 := by rw [Nat.floor_add_one positive.le, Nat.floor_eq_zero.mpr small]
  have continuous : Continuous f := by
    have smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 f := by
      simpa only [floor, Nat.cast_one] using regular.differentiable
    exact smooth.continuous
  let K := fun p : I × I => patch p.1 ∩ f ⁻¹' patch p.2
  have compactK (p : I × I) : IsCompact (K p) :=
    (compact p.1).inter_right ((compact p.2).isClosed.preimage continuous)
  have estimates (p : I × I) := regular.compact_native_cocycle_holder positive small
    (centers p.1) (centers p.2) (K p) (compactK p)
    (fun _ hx => inside p.1 hx.1) (fun _ hx => inside p.2 hx.2)
  choose C nonnegative bound using estimates
  refine ⟨∑ p, C p, Finset.sum_nonneg (fun p _ => nonnegative p), ?_⟩
  intro i j x hx y hy imageX imageY
  have individual := bound (i, j) x ⟨hx, imageX⟩ y ⟨hy, imageY⟩
  have constant := Finset.single_le_sum (fun p (_ : p ∈ Finset.univ) => nonnegative p)
    (Finset.mem_univ (i, j))
  exact individual.trans (mul_le_mul_of_nonneg_right constant (Real.rpow_nonneg dist_nonneg _))

end LeanShared.FractionalManifoldRegularity
