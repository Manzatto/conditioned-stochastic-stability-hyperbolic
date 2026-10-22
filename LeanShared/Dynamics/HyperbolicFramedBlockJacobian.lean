module

public import LeanShared.Dynamics.HyperbolicIsometricFraming
public import LeanShared.Dynamics.HyperbolicUnstableBlockJacobian

/-! The expanding block retained by actual coherent finite shooting has
exact determinant equal to the literal unstable-Jacobian product. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet.IsometricFraming
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}

set_option maxHeartbeats 1600000 in
theorem expanding_abs_det (a : IsometricFraming h)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (n : ℕ) (x : Λ)
    (U : EuclideanSpace ℝ (Fin a.unstableDimension) →L[ℝ] EuclideanSpace ℝ (Fin a.unstableDimension))
    (S : EuclideanSpace ℝ (Fin a.stableDimension) →L[ℝ] EuclideanSpace ℝ (Fin a.stableDimension))
    (actual : ∀ z, (a.whole (h.iteratePoint n x)).symm
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^n : M ≃ₜ M) : M → M) x.val (a.whole x z)) =
      (U z.1, S z.2)) :
    |U.toLinearMap.det| = ∏ j ∈ Finset.range n, h.unstableJacobian ((T : M → M)^[j] x.val) := by
  apply h.framed_unstable_block_abs_det forward inverse n x.val x.property
    (a.unstable x) (a.unstable (h.iteratePoint n x)) U.toLinearMap
  intro v
  have action := congrArg (a.whole (h.iteratePoint n x)) (actual (v, 0))
  have cancellation := (a.whole (h.iteratePoint n x)).apply_symm_apply
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^n : M ≃ₜ M) : M → M) x.val (a.whole x (v, 0)))
  have action := cancellation.symm.trans action
  simp only [a.whole_apply, map_zero, Submodule.coe_zero, add_zero] at action
  exact action.symm

end LeanShared.HyperbolicBasicSet.IsometricFraming
