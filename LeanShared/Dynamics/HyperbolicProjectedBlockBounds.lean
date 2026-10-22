module
public import LeanShared.Dynamics.HyperbolicTangentBlockBounds
public import LeanShared.Geometry.CompactRiemannianEndomorphisms

/-! Actual stable and complementary unstable projections have uniform
native Riemannian norm bounds. A single actual iterate makes the FULL
projected forward/backward operators arbitrarily small; no adapted metric
or projected contraction source is supplied. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem HyperbolicData.exists_projection_norm_bound (h : HyperbolicData (E := E) T Λ) :
    ∃ B > 0, ∀ x ∈ Λ, ‖h.projection x‖ ≤ B ∧
      ‖ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ, E)) x) - h.projection x‖ ≤ B := by
  obtain ⟨C, positiveC, bound⟩ := CompactRiemannianEndomorphisms.exists_norm_bound
    (fun x : M => TangentSpace (𝓘(ℝ, E)) x) Λ h.compact h.projection h.continuous_splitting
  refine ⟨1 + C, by positivity, fun x hx => ⟨?_, ?_⟩⟩
  · linarith [bound x hx]
  · exact (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le (bound x hx))

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.exists_projected_block_bound
    (h : HyperbolicData (E := E) T Λ) (κ : ℝ) (positiveκ : 0 < κ) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ,
      ‖(mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T : M → M)^[N]) x).comp (h.projection x)‖ ≤ κ ∧
      ‖(mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T.symm : M → M)^[N]) x).comp
        (ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ, E)) x) - h.projection x)‖ ≤ κ := by
  obtain ⟨B, positiveB, bounds⟩ := h.exists_projection_norm_bound
  have limit : Tendsto (fun n : ℕ => h.constant * h.contraction ^ n * B) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one h.contraction_pos.le h.contraction_lt_one)).mul_const B
  have small := (tendsto_order.mp limit).2 κ positiveκ
  obtain ⟨N, positiveN, estimate⟩ := ((eventually_gt_atTop 0).and small).exists
  have coefficient : 0 ≤ h.constant * h.contraction ^ N := by
    exact mul_nonneg h.constant_pos.le (pow_nonneg h.contraction_pos.le _)
  refine ⟨N, positiveN, fun x hx => ⟨?_, ?_⟩⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ positiveκ.le
    intro v
    have member : h.projection x v ∈ h.stable x := by
      rw [← h.projection_range x hx]
      exact LinearMap.mem_range.mpr ⟨v, rfl⟩
    calc
      _ ≤ h.constant * h.contraction ^ N * ‖h.projection x v‖ := h.stable_bound N x hx _ member
      _ ≤ h.constant * h.contraction ^ N * (B * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((h.projection x).le_opNorm v |>.trans
          (mul_le_mul_of_nonneg_right (bounds x hx).1 (norm_nonneg _))) coefficient
      _ ≤ κ * ‖v‖ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right estimate.le (norm_nonneg _)
  · apply ContinuousLinearMap.opNorm_le_bound _ positiveκ.le
    intro v
    let Q := ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ, E)) x) - h.projection x
    have member : Q v ∈ h.unstable x := by
      rw [← h.projection_kernel x hx]
      change h.projection x (v - h.projection x v) = 0
      rw [map_sub, show h.projection x (h.projection x v) = h.projection x v from
        congrArg (fun L => L v) (h.projection_idempotent x hx), sub_self]
    calc
      _ ≤ h.constant * h.contraction ^ N * ‖Q v‖ := h.unstable_bound N x hx _ member
      _ ≤ h.constant * h.contraction ^ N * (B * ‖v‖) :=
        mul_le_mul_of_nonneg_left (Q.le_opNorm v |>.trans
          (mul_le_mul_of_nonneg_right (bounds x hx).2 (norm_nonneg _))) coefficient
      _ ≤ κ * ‖v‖ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right estimate.le (norm_nonneg _)

end LeanShared.HyperbolicBasicSet
