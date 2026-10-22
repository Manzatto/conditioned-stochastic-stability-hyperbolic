module
public import LeanShared.Dynamics.BasicHyperbolicForwardBlockBowen
public import LeanShared.Dynamics.BlockBowenTransfer

/-! The usual one-step Bowen property is derived from literal hyperbolic
basic data and actual positive fractional regularity of the observable.
Neither a Hölder constant, a distortion bound nor shadowing is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal BigOperators
open ThermodynamicDefinitions

set_option maxHeartbeats 2400000 in
theorem BasicData.bowen_distortion
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ) :
    ∃ η > 0, ∃ D ≥ 0, ∀ (n : ℕ) (x : M), x ∈ Λ → ∀ (y : M), y ∈ Λ →
      (∀ j < n, dist (((T : M → M)^[j]) x) (((T : M → M)^[j]) y) < η) →
      |orbitSum T ψ n x - orbitSum T ψ n y| ≤ D := by
  obtain ⟨N, positiveN, η, positiveη, D, nonnegativeD, distortion⟩ :=
    b.forward_block_bowen forward inverse ψ α positiveα smallα regular
  have invariant : MapsTo T Λ Λ := by
    intro x hx
    rw [← b.hyperbolic.invariant]
    exact mem_image_of_mem T hx
  have continuous : Continuous ψ := regular.differentiable.continuous
  obtain ⟨B, positiveB, bounded⟩ :=
    (b.hyperbolic.compact.image continuous).isBounded.exists_pos_norm_le
  have bound (x : M) (hx : x ∈ Λ) : |ψ x| ≤ B := by
    simpa only [Real.norm_eq_abs] using bounded (ψ x) ⟨x, hx, rfl⟩
  refine ⟨η, positiveη, (N : ℝ) * D + 2 * N * B, by positivity, ?_⟩
  apply one_step_bowen_of_blocks T Λ invariant ψ B D η positiveB.le bound N positiveN
  intro q x hx y _ close
  cases q with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, sub_self, abs_zero] using nonnegativeD
  | succ q =>
    exact distortion q ⟨x, hx⟩ y (fun j hj => close j (by omega))

end LeanShared.HyperbolicBasicSet
