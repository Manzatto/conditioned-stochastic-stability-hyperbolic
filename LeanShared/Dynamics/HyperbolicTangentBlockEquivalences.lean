module
public import LeanShared.Dynamics.HyperbolicTangentBlockBounds
public import LeanShared.Geometry.InvariantTangentBlockEquivalence

/-! Contracting hyperbolic blocks are constructed on the ACTUAL invariant
stable/unstable tangent fibers. One common block length gives a stable block
and inverse unstable block with any requested small operator norm. Forward
and inverse actions are exactly derivatives of the actual iterated map.
No block cocycle, rank assumption or graph-transform conclusion is supplied. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

set_option maxHeartbeats 2400000 in
theorem HyperbolicData.exists_actual_tangent_blocks
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (κ : ℝ) (positive : 0 < κ) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ,
      ∃ S : h.stable x ≃L[ℝ] h.stable ((T^N) x),
      ∃ U : h.unstable x ≃L[ℝ] h.unstable ((T^N) x),
        ‖S.toContinuousLinearMap‖ ≤ κ ∧ ‖U.symm.toContinuousLinearMap‖ ≤ κ ∧
        (∀ v, (S v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M) x v.val) ∧
        (∀ v, (U v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M) x v.val) ∧
        (∀ v, (U.symm v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
          ((T^N).symm : M → M) ((T^N) x) v.val) := by
  have preserves : MapsTo T Λ Λ := fun x hx => by
    rw [← h.invariant]
    exact mem_image_of_mem T hx
  obtain ⟨N, positiveN, bounds⟩ := h.exists_tangent_block_bound κ positive
  refine ⟨N, positiveN, fun x hx => ?_⟩
  obtain ⟨S, stableAction, _⟩ := InvariantTangentDistributionIterates.exists_block_equivalence
    T forward inverse Λ preserves h.stable h.stable_invariant N x hx
  obtain ⟨U, unstableAction, inverseAction⟩ := InvariantTangentDistributionIterates.exists_block_equivalence
    T forward inverse Λ preserves h.unstable h.unstable_invariant N x hx
  have targetMember : (T^N) x ∈ Λ := by
    rw [DiffeomorphismIterates.coe_pow]
    exact preserves.iterate N hx
  have stableBound := (bounds x hx).1
  rw [← DiffeomorphismIterates.coe_pow T N] at stableBound
  have inverseBound := (bounds ((T^N) x) targetMember).2
  rw [← DiffeomorphismIterates.coe_symm_pow T N] at inverseBound
  refine ⟨S, U, ?_, ?_, stableAction, unstableAction, inverseAction⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ positive.le
    intro v
    change ‖(S v).val‖ ≤ κ * ‖v‖
    rw [stableAction]
    exact (((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M) x).comp
      (h.stable x).subtypeL).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right stableBound (norm_nonneg v))
  · apply ContinuousLinearMap.opNorm_le_bound _ positive.le
    intro v
    change ‖(U.symm v).val‖ ≤ κ * ‖v‖
    rw [inverseAction]
    have estimate := (((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N).symm : M → M) ((T^N) x)).comp
      (h.unstable ((T^N) x)).subtypeL).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right inverseBound (norm_nonneg v))
    have metric_transport (y : M) (same : y = x) (w : TangentSpace (𝓘(ℝ, E)) y) :
        ‖w‖ = ‖(show TangentSpace (𝓘(ℝ, E)) x from w)‖ := by
      subst y
      rfl
    rw [metric_transport _ ((T^N).symm_apply_apply x) _] at estimate
    exact estimate

end LeanShared.HyperbolicBasicSet
