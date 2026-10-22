module

public import LeanShared.Dynamics.HyperbolicUnstableJacobianCocycle

/-! The actual orbit potential has exactly the literal iterated weight
divided by the genuine unstable derivative's norm determinant. Positivity
is needed only on the invariant core, where every orbit observation lies. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle ThermodynamicDefinitions
open scoped Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem HyperbolicData.exp_orbit_potential (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (g : M → ℝ) (positive : ∀ x ∈ Λ, 0 < g x) (n : ℕ) (x : M) (hx : x ∈ Λ) :
    Real.exp (orbitSum T (h.potential g) n x) =
      (∏ j ∈ Finset.range n, g ((T : M → M)^[j] x)) /
        (h.unstableCocycle forward inverse x hx n).toLinearMap.normDet := by
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp h.invariant.subset
  rw [h.unstableCocycle_normDet forward inverse x hx n, ← Finset.prod_div_distrib]
  change Real.exp (∑ j ∈ Finset.range n, h.potential g ((T : M → M)^[j] x)) = _
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  change Real.exp (Real.log (g ((T : M → M)^[j] x)) -
    Real.log (h.unstableJacobian ((T : M → M)^[j] x))) = _
  rw [Real.exp_sub, Real.exp_log (positive _ (invariant.iterate j hx)),
    Real.exp_log (h.unstableJacobian_positive forward inverse _ (invariant.iterate j hx))]

end LeanShared.HyperbolicBasicSet
