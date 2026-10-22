module
public import LeanShared.Dynamics.HyperbolicUnstableBlockJacobian
public import LeanShared.Dynamics.HyperbolicOrbitPotentialProduct
public import LeanShared.Dynamics.HyperbolicNormedAdaptedProjection

/-! The literal native determinant in the intrinsic principal row has the
exact thermodynamic normalization on the core. The extended projector is
identified with the actual unstable space there; no chart density factor
or independent Jacobian comparison is assumed. -/
@[expose] public noncomputable section
namespace LeanShared.HyperbolicBasicSet.HyperbolicData
open Set IsManifold Bundle ThermodynamicDefinitions
open scoped Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem native_unstable_iterate_normDet (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (n : ℕ) (x : M) (hx : x ∈ Λ) :
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[n]) x).toLinearMap.domRestrict
      (h.unstable x)).normDet =
        ∏ j ∈ Finset.range n, h.unstableJacobian ((T : M → M)^[j] x) := by
  have preserves : MapsTo T Λ Λ := image_subset_iff.mp h.invariant.subset
  obtain ⟨A,actual,_⟩ := InvariantTangentDistributionIterates.exists_block_equivalence
    T forward inverse Λ preserves h.unstable h.unstable_invariant n x hx
  let D := (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T^n : M ≃ₜ M) : M → M) x).toLinearMap
  have into (v : h.unstable x) : D v ∈ h.unstable ((T^n) x) := by
    change mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T^n : M ≃ₜ M) : M → M) x v.val ∈ _
    rw [← actual v]
    exact (A v).property
  have equal : (D.domRestrict (h.unstable x)).codRestrict (h.unstable ((T^n) x)) into =
      A.toLinearMap := by
    ext v
    exact (actual v).symm
  have determinant : (D.domRestrict (h.unstable x)).normDet = A.toLinearMap.normDet := by
    rw [← LinearMap.normDet_codRestrict into,equal]
  have product := determinant.trans (h.unstable_block_normDet forward inverse n x hx A actual)
  have sameCost := congrArg (fun f : M → M =>
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).toLinearMap.domRestrict (h.unstable x)).normDet)
      (DiffeomorphismIterates.coe_pow T n)
  exact sameCost.symm.trans product

variable [CompactSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

def nativePressureJacobian (h : HyperbolicData (E := E) T Λ) (n : ℕ) (x : M) : ℝ :=
  ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[n]) x).toLinearMap.domRestrict
    (h.normedAdaptedProjection.unstable x)).normDet

theorem nativePressureJacobian_eq (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (n : ℕ) (x : M) (hx : x ∈ Λ) :
    h.nativePressureJacobian n x =
      ∏ j ∈ Finset.range n, h.unstableJacobian ((T : M → M)^[j] x) := by
  have domain_congr (U W : Submodule ℝ (TangentSpace (𝓘(ℝ,E)) x)) (same : U = W) :
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[n]) x).toLinearMap.domRestrict U).normDet =
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[n]) x).toLinearMap.domRestrict W).normDet := by
    subst W
    rfl
  exact (domain_congr _ _ (h.normedAdaptedProjection.unstable_core x hx)).trans
    (h.native_unstable_iterate_normDet forward inverse n x hx)

theorem nativePressureJacobian_pos (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (n : ℕ) (x : M) (hx : x ∈ Λ) : 0 < h.nativePressureJacobian n x := by
  rw [h.nativePressureJacobian_eq forward inverse n x hx]
  have preserves : MapsTo T Λ Λ := image_subset_iff.mp h.invariant.subset
  exact Finset.prod_pos (fun j _ => h.unstableJacobian_positive forward inverse _
    (preserves.iterate j hx))

theorem native_weight_div_jacobian (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (g : M → ℝ) (positive : ∀ x ∈ Λ, 0 < g x) (n : ℕ) (x : M) (hx : x ∈ Λ) :
    (∏ j ∈ Finset.range n, g ((T : M → M)^[j] x)) / h.nativePressureJacobian n x =
      Real.exp (orbitSum T (h.potential g) n x) := by
  rw [h.nativePressureJacobian_eq forward inverse n x hx]
  have exactRatio := h.exp_orbit_potential forward inverse g positive n x hx
  rw [h.unstableCocycle_normDet forward inverse x hx n] at exactRatio
  exact exactRatio.symm

end LeanShared.HyperbolicBasicSet.HyperbolicData
