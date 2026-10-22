module

public import LeanShared.Dynamics.HyperbolicUnstableReturn
public import LeanShared.Geometry.InvariantTangentBlockEquivalence
public import LeanShared.LinearAlgebra.ComplementaryDeterminant

/-! Genuine periodic tangent return blocks and their full determinant
factorization, derived from literal hyperbolic invariant subspaces and the
actual manifold derivative. No periodic block or trace identity is supplied. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

set_option maxHeartbeats 2200000 in
theorem HyperbolicData.exists_periodic_return_blocks (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (p : ℕ) (x : M) (hx : x ∈ Λ) (fixed : (T : M → M)^[p] x = x) :
    ∃ A : TangentSpace (𝓘(ℝ,E)) x ≃L[ℝ] TangentSpace (𝓘(ℝ,E)) x,
    ∃ S : h.stable x ≃L[ℝ] h.stable x, ∃ U : h.unstable x ≃L[ℝ] h.unstable x,
      (∀ v, A v = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[p]) x v) ∧
      (∀ v, (S v).val = A v.val) ∧ (∀ v, (U v).val = A v.val) ∧
      U.toLinearMap.normDet = ∏ j ∈ Finset.range p, h.unstableJacobian ((T : M → M)^[j] x) ∧
      (LinearMap.id - A.toLinearMap).det =
        (LinearMap.id - S.toLinearMap).det * (LinearMap.id - U.toLinearMap).det := by
  have fixedPow : (T ^ p) x = x := by simpa only [DiffeomorphismIterates.coe_pow] using fixed
  let forwardP := DiffeomorphismIterates.mdifferentiable_pow T forward p
  let inverseP := DiffeomorphismIterates.mdifferentiable_symm_pow T inverse p
  let D := DiffeomorphismDifferential.differential (T ^ p) forwardP inverseP x
  let transport (y : M) (same : y = x) : TangentSpace (𝓘(ℝ,E)) y ≃ₗᵢ[ℝ] TangentSpace (𝓘(ℝ,E)) x := by
    subst y
    exact LinearIsometryEquiv.refl ℝ _
  have transportAction (y : M) (same : y = x) (v : TangentSpace (𝓘(ℝ,E)) y) : transport y same v = v := by
    subst y
    rfl
  let A := D.trans (transport ((T ^ p) x) fixedPow).toContinuousLinearEquiv
  have derivativeSame (v : E) :
      mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T ^ p : M ≃ₜ M) : M → M) x v =
        mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[p]) x v :=
    congrArg (fun L : E →L[ℝ] E => L v)
      (mfderiv_congr (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (x := x) (DiffeomorphismIterates.coe_pow T p))
  have actualA (v : TangentSpace (𝓘(ℝ,E)) x) :
      A v = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[p]) x v := by
    change transport ((T ^ p) x) fixedPow (D v) = _
    rw [transportAction ((T ^ p) x) fixedPow (D v)]
    have actual := DiffeomorphismDifferential.differential_apply (T ^ p) forwardP inverseP x v
    exact actual.trans (derivativeSame v)
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp h.invariant.subset
  obtain ⟨S₀, actualS₀, _⟩ := InvariantTangentDistributionIterates.exists_block_equivalence
    T forward inverse Λ invariant h.stable h.stable_invariant p x hx
  let stableTransport (y : M) (same : y = x) : h.stable y ≃ₗᵢ[ℝ] h.stable x := by
    subst y
    exact LinearIsometryEquiv.refl ℝ _
  have stableAction (y : M) (same : y = x) (v : h.stable y) : (stableTransport y same v).val = v.val := by
    subst y
    rfl
  let S := S₀.trans (stableTransport ((T ^ p) x) fixedPow).toContinuousLinearEquiv
  let U := h.unstableReturn forward inverse p x hx fixed
  have actualS (v : h.stable x) : (S v).val = A v.val := by
    change (stableTransport ((T ^ p) x) fixedPow (S₀ v)).val = _
    exact (stableAction ((T ^ p) x) fixedPow (S₀ v)).trans
      ((actualS₀ v).trans ((derivativeSame v.val).trans (actualA v.val).symm))
  have actualU (v : h.unstable x) : (U v).val = A v.val := by
    rw [actualA]
    exact h.unstableReturn_apply forward inverse p x hx fixed v
  refine ⟨A, S, U, actualA, actualS, actualU,
    h.unstableReturn_normDet forward inverse p x hx fixed, ?_⟩
  let e := (h.stable x).prodEquivOfIsCompl (h.unstable x) (h.complementary x hx)
  apply ComplementaryDeterminant.one_sub e
  intro s u
  change A (s.val + u.val) = (S s).val + (U u).val
  rw [map_add, actualS, actualU]

end LeanShared.HyperbolicBasicSet
