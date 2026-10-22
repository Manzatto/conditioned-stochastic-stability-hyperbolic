module

public import LeanShared.Dynamics.HyperbolicThermodynamics
public import LeanShared.Geometry.DiffeomorphismDifferential

/-! The actual unstable differential is a genuine linear equivalence,
and its actual norm determinant equals the literal unstable Jacobian. -/
public noncomputable section
open Set Function IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}
namespace HyperbolicData

@[expose] def unstableDifferential (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (x : M) (inside : x ∈ Λ) : h.unstable x ≃L[ℝ] h.unstable (T x) := by
  let D := DiffeomorphismDifferential.differential T forward inverse x
  have same : D.toLinearMap=(mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap := by
    ext v
    exact DiffeomorphismDifferential.differential_apply T forward inverse x v
  exact D.ofSubmodules (h.unstable x) (h.unstable (T x))
    (by rw [same]; exact h.unstable_invariant x inside)

omit [FiniteDimensional ℝ E] in
theorem unstableDifferential_apply (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (x : M) (inside : x ∈ Λ) (v : h.unstable x) :
    (h.unstableDifferential forward inverse x inside v).val =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v.val := rfl

theorem unstableJacobian_eq_normDet (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (x : M) (inside : x ∈ Λ) :
    h.unstableJacobian x=(h.unstableDifferential forward inverse x inside).toLinearMap.normDet := by
  let F : h.unstable x →ₗ[ℝ] TangentSpace (𝓘(ℝ, E)) (T x) :=
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap.comp (h.unstable x).subtype
  have lhs : h.unstableJacobian x=F.normDet := by
    unfold unstableJacobian
    exact LinearMap.normDet_codRestrict _
  have insideTarget (v : h.unstable x) : F v ∈ h.unstable (T x) := by
    rw [←h.unstable_invariant x inside]
    exact Submodule.mem_map.mpr ⟨v.val,v.property,rfl⟩
  have equality : (h.unstableDifferential forward inverse x inside).toLinearMap =
      F.codRestrict (h.unstable (T x)) insideTarget := by
    ext v
    exact h.unstableDifferential_apply forward inverse x inside v
  rw [lhs,equality,LinearMap.normDet_codRestrict]

theorem unstableJacobian_positive (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (x : M) (inside : x ∈ Λ) : 0 < h.unstableJacobian x := by
  rw [h.unstableJacobian_eq_normDet forward inverse x inside]
  apply lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm ?_)
  intro zero
  exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
    (LinearMap.ker_eq_bot.mpr (h.unstableDifferential forward inverse x inside).injective)

end HyperbolicData
end LeanShared.HyperbolicBasicSet
