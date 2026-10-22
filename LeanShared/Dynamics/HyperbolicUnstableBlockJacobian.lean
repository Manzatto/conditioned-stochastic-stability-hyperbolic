module

public import LeanShared.Dynamics.HyperbolicUnstableJacobianCocycle
public import LeanShared.Geometry.InvariantTangentBlockEquivalence
public import LeanShared.Geometry.IsometricFramedJacobian

/-! Any actual unstable differential block has exactly the product of
literal one-step unstable Jacobians, including blocks written in native
isometric coordinate frames. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet.HyperbolicData
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem unstable_block_normDet (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (n : ℕ) (x : M) (hx : x ∈ Λ)
    (A : h.unstable x ≃L[ℝ] h.unstable ((T^n) x))
    (actual : ∀ v, (A v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      ((T^n : M ≃ₜ M) : M → M) x v.val) :
    A.toLinearMap.normDet = ∏ j ∈ Finset.range n, h.unstableJacobian ((T : M → M)^[j] x) := by
  have samePoint : cocyclePoint T x n = (T^n) x := by
    rw [cocyclePoint_eq_iterate, DiffeomorphismIterates.coe_pow]
  have transport (y : M) (same : y = (T^n) x)
      (D : h.unstable x ≃L[ℝ] h.unstable y)
      (action : ∀ v, (D v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
        ((T^n : M ≃ₜ M) : M → M) x v.val) : D.toLinearMap.normDet = A.toLinearMap.normDet := by
    subst y
    have equality : D = A := by
      apply DFunLike.ext
      intro v
      apply Subtype.ext
      rw [action, actual]
    rw [equality]
  have comparison := transport _ samePoint (h.unstableCocycle forward inverse x hx n)
    (fun v => by
      rw [h.unstableCocycle_apply forward inverse x hx n v, DiffeomorphismIterates.coe_pow])
  exact comparison.symm.trans (h.unstableCocycle_normDet forward inverse x hx n)

set_option maxHeartbeats 1600000 in
theorem framed_unstable_block_abs_det
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (n : ℕ) (x : M) (hx : x ∈ Λ)
    (e : U ≃ₗᵢ[ℝ] h.unstable x) (f : U ≃ₗᵢ[ℝ] h.unstable ((T^n) x))
    (L : U →ₗ[ℝ] U)
    (actual : ∀ v, (f (L v)).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      ((T^n : M ≃ₜ M) : M → M) x (e v).val) :
    |L.det| = ∏ j ∈ Finset.range n, h.unstableJacobian ((T : M → M)^[j] x) := by
  have preserves : MapsTo T Λ Λ := image_subset_iff.mp h.invariant.subset
  obtain ⟨A, action, _⟩ := InvariantTangentDistributionIterates.exists_block_equivalence
    T forward inverse Λ preserves h.unstable h.unstable_invariant n x hx
  have equality : |L.det| = A.toLinearMap.normDet :=
    IsometricFramedJacobian.eq_normDet e f A.toLinearMap L (fun v => by
      apply Subtype.ext
      exact (actual v).trans (action (e v)).symm)
  exact equality.trans (h.unstable_block_normDet forward inverse n x hx A action)

end LeanShared.HyperbolicBasicSet.HyperbolicData
