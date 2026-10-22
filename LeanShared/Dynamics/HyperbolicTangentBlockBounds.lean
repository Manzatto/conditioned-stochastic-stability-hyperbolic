module
public import LeanShared.Dynamics.HyperbolicBasicSet
public import Mathlib.Analysis.SpecificLimits.Basic

/-! A genuine common block length for the actual hyperbolic tangent cocycle.
The exponential bounds in HyperbolicData produce arbitrarily small stable and
inverse-unstable operator norms, uniformly on the basic set. No one-step
adapted contraction or unrelated linear cocycle is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.exists_tangent_block_bound
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (κ : ℝ) (positive : 0 < κ) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ,
      ‖(mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T : M → M)^[N]) x).comp
        (h.stable x).subtypeL‖ ≤ κ ∧
      ‖(mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T.symm : M → M)^[N]) x).comp
        (h.unstable x).subtypeL‖ ≤ κ := by
  have limit : Tendsto (fun n : ℕ => h.constant * h.contraction^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one h.contraction_pos.le h.contraction_lt_one)
  have small := (tendsto_order.mp limit).2 κ positive
  obtain ⟨N, positiveN, estimate⟩ := ((eventually_gt_atTop 0).and small).exists
  refine ⟨N, positiveN, fun x hx => ⟨?_, ?_⟩⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ positive.le
    intro v
    exact (h.stable_bound N x hx v.val v.property).trans
      (mul_le_mul_of_nonneg_right estimate.le (norm_nonneg v))
  · apply ContinuousLinearMap.opNorm_le_bound _ positive.le
    intro v
    exact (h.unstable_bound N x hx v.val v.property).trans
      (mul_le_mul_of_nonneg_right estimate.le (norm_nonneg v))

end LeanShared.HyperbolicBasicSet
