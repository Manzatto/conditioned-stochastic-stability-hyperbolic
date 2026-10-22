module

public import LeanShared.Dynamics.HyperbolicPeriodicReturnBlocks
public import LeanShared.Dynamics.HyperbolicUnstableReturnInverse

/-! Both actual periodic stable and inverse-unstable native blocks inherit the literal exponential hyperbolic bound. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

set_option maxHeartbeats 1800000 in
theorem HyperbolicData.exists_periodic_return_bounds (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (p : ℕ) (x : M) (hx : x ∈ Λ) (fixed : (T : M → M)^[p] x = x) :
    ∃ A : TangentSpace (𝓘(ℝ,E)) x ≃L[ℝ] TangentSpace (𝓘(ℝ,E)) x,
    ∃ S : h.stable x ≃L[ℝ] h.stable x, ∃ U : h.unstable x ≃L[ℝ] h.unstable x,
      (∀ v, A v = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[p]) x v) ∧
      U.toLinearMap.normDet = ∏ j ∈ Finset.range p, h.unstableJacobian ((T : M → M)^[j] x) ∧
      (LinearMap.id - A.toLinearMap).det =
        (LinearMap.id - S.toLinearMap).det * (LinearMap.id - U.toLinearMap).det ∧
      ‖S.toContinuousLinearMap‖ ≤ h.constant * h.contraction ^ p ∧
      ‖U.symm.toContinuousLinearMap‖ ≤ h.constant * h.contraction ^ p := by
  obtain ⟨A, S, U, actualA, actualS, actualU, determinantU, determinant⟩ :=
    h.exists_periodic_return_blocks forward inverse p x hx fixed
  refine ⟨A, S, U, actualA, determinantU, determinant, ?_, ?_⟩
  · have metricTransport (y : M) (same : y = x) (w : TangentSpace (𝓘(ℝ,E)) y) :
        ‖w‖ = ‖(show TangentSpace (𝓘(ℝ,E)) x from w)‖ := by
      subst y
      rfl
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg h.constant_pos.le (pow_nonneg h.contraction_pos.le p))
    intro v
    change ‖(S v).val‖ ≤ _
    have bound := h.stable_bound p x hx v.val v.property
    rw [metricTransport _ fixed _] at bound
    have scalar : (S v).val = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[p]) x v.val :=
      (actualS v).trans (actualA v.val)
    exact (congrArg (fun w : TangentSpace (𝓘(ℝ,E)) x => ‖w‖) scalar).trans_le bound
  · have same : U = h.unstableReturn forward inverse p x hx fixed := by
      apply DFunLike.ext
      intro v
      apply Subtype.ext
      exact ((actualU v).trans (actualA v.val)).trans
        (h.unstableReturn_apply forward inverse p x hx fixed v).symm
    rw [same]
    exact h.unstableReturn_inverse_norm_le forward inverse p x hx fixed

end LeanShared.HyperbolicBasicSet
