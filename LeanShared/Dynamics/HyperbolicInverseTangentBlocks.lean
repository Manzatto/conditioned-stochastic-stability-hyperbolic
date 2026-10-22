module
public import LeanShared.Dynamics.HyperbolicTangentBlockBounds
public import LeanShared.Geometry.InvariantTangentDistributionInverse
public import LeanShared.Geometry.InvariantTangentBlockEquivalence

/-! Contracting reverse-time hyperbolic blocks are constructed on the ACTUAL invariant
stable/unstable tangent fibers. One common block length gives a stable block
and inverse unstable block with any requested small operator norm. Forward
and inverse actions are exactly derivatives of the actual iterated map.
No block cocycle, rank assumption or graph-transform conclusion is supplied. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

set_option maxHeartbeats 2400000 in
theorem HyperbolicData.exists_actual_inverse_tangent_blocks
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (κ : ℝ) (positive : 0 < κ) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ,
      ∃ S : h.unstable x ≃L[ℝ] h.unstable ((T.symm^N) x),
      ∃ U : h.stable x ≃L[ℝ] h.stable ((T.symm^N) x),
        ‖S.toContinuousLinearMap‖ ≤ κ ∧ ‖U.symm.toContinuousLinearMap‖ ≤ κ ∧
        (∀ v, (S v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T.symm^N : M ≃ₜ M) : M → M) x v.val) ∧
        (∀ v, (U v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T.symm^N : M ≃ₜ M) : M → M) x v.val) ∧
        (∀ v, (U.symm v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
          ((T.symm^N).symm : M → M) ((T.symm^N) x) v.val) := by
  have preserves : MapsTo T.symm Λ Λ := by
    intro x hx
    rw [←h.invariant] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    simpa only [T.symm_apply_apply] using hy
  have stableInvariant := InvariantTangentDistributionIterates.map_inverse T forward inverse Λ h.invariant
    h.unstable h.unstable_invariant
  have unstableInvariant := InvariantTangentDistributionIterates.map_inverse T forward inverse Λ h.invariant
    h.stable h.stable_invariant
  obtain ⟨N, positiveN, bounds⟩ := h.exists_tangent_block_bound κ positive
  refine ⟨N, positiveN, fun x hx => ?_⟩
  obtain ⟨S, stableAction, _⟩ := InvariantTangentDistributionIterates.exists_block_equivalence
    T.symm inverse forward Λ preserves h.unstable stableInvariant N x hx
  obtain ⟨U, unstableAction, inverseAction⟩ := InvariantTangentDistributionIterates.exists_block_equivalence
    T.symm inverse forward Λ preserves h.stable unstableInvariant N x hx
  have targetMember : (T.symm^N) x ∈ Λ := by
    rw [DiffeomorphismIterates.coe_pow]
    exact preserves.iterate N hx
  have stableBound := (bounds x hx).2
  rw [←DiffeomorphismIterates.coe_pow T.symm N] at stableBound
  have inverseBound := (bounds ((T.symm^N) x) targetMember).1
  have back : ((T.symm^N).symm : M → M)=(T : M → M)^[N] := by
    simpa only [Homeomorph.symm_symm] using DiffeomorphismIterates.coe_symm_pow T.symm N
  rw [←back] at inverseBound
  refine ⟨S, U, ?_, ?_, stableAction, unstableAction, inverseAction⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ positive.le
    intro v
    change ‖(S v).val‖ ≤ κ * ‖v‖
    rw [stableAction]
    exact (((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T.symm^N : M ≃ₜ M) : M → M) x).comp
      (h.unstable x).subtypeL).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right stableBound (norm_nonneg v))
  · apply ContinuousLinearMap.opNorm_le_bound _ positive.le
    intro v
    change ‖(U.symm v).val‖ ≤ κ * ‖v‖
    rw [inverseAction]
    have estimate := (((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T.symm^N).symm : M → M) ((T.symm^N) x)).comp
      (h.stable ((T.symm^N) x)).subtypeL).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right inverseBound (norm_nonneg v))
    have metric_transport (y : M) (same : y = x) (w : TangentSpace (𝓘(ℝ, E)) y) :
        ‖w‖ = ‖(show TangentSpace (𝓘(ℝ, E)) x from w)‖ := by
      subst y
      rfl
    rw [metric_transport _ ((T.symm^N).symm_apply_apply x) _] at estimate
    exact estimate

end LeanShared.HyperbolicBasicSet
