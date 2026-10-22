module

public import LeanShared.Dynamics.HyperbolicOrbitPotentialProduct

/-! Literal finite orbit weights split multiplicatively into the actual
thermodynamic energy and unstable Jacobian, with core-only positivity. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle ThermodynamicDefinitions
open scoped Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem HyperbolicData.orbit_weight_eq_energy_jacobian (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (g : M → ℝ) (positive : ∀ x ∈ Λ, 0 < g x) (n : ℕ) (x : M) (hx : x ∈ Λ) :
    Real.exp (orbitSum T (h.potential g) n x) *
      (∏ j ∈ Finset.range n, h.unstableJacobian ((T : M → M)^[j] x)) =
      ∏ j ∈ Finset.range n, g ((T : M → M)^[j] x) := by
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp h.invariant.subset
  have nonzero : (∏ j ∈ Finset.range n, h.unstableJacobian ((T : M → M)^[j] x)) ≠ 0 :=
    (Finset.prod_pos (fun j hj => h.unstableJacobian_positive forward inverse _ (invariant.iterate j hx))).ne'
  have formula := h.exp_orbit_potential forward inverse g positive n x hx
  rw [h.unstableCocycle_normDet forward inverse x hx n] at formula
  exact (eq_div_iff nonzero).mp formula

end LeanShared.HyperbolicBasicSet
