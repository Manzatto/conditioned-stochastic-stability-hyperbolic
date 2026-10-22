module

public import LeanShared.Geometry.DiffeomorphismInverseDifferential
public import Mathlib.Algebra.Module.Submodule.Map

/-! Genuine tangent-distribution invariance under a diffeomorphism implies
invariance under the actual inverse derivative. No inverse-invariance source
is required. -/
public noncomputable section
open Set IsManifold
open scoped Manifold
namespace LeanShared.InvariantTangentDistributionIterates
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

private theorem inverse_at_image (T : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (S : ∀ x, Submodule ℝ (TangentSpace (𝓘(ℝ,E)) x))
    (x : M) (invariant : (S x).map (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T x).toLinearMap=S (T x)) :
    (S (T x)).map (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm (T x)).toLinearMap=S x := by
  let D := DiffeomorphismDifferential.differential T forward inverse x
  have same : D.toLinearMap=(mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T x).toLinearMap := by
    ext v
    rfl
  have back : D.symm.toLinearMap=(mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm (T x)).toLinearMap := by
    ext v
    exact DiffeomorphismDifferential.differential_symm_apply T forward inverse x v
  have identity : D.symm.toLinearMap.comp D.toLinearMap=LinearMap.id := by
    ext v
    exact D.symm_apply_apply v
  have mapped : (S x).map D.toLinearMap=S (T x) :=
    (congrArg (fun A : TangentSpace (𝓘(ℝ,E)) x →ₗ[ℝ] TangentSpace (𝓘(ℝ,E)) (T x) =>
      (S x).map A) same).trans invariant
  have composed := Submodule.map_comp D.toLinearMap D.symm.toLinearMap (S x)
  have reverse : (S (T x)).map D.symm.toLinearMap=S x := by
    have replace := congrArg (fun Q : Submodule ℝ (TangentSpace (𝓘(ℝ,E)) (T x)) =>
      Q.map D.symm.toLinearMap) mapped
    exact replace.symm.trans (composed.symm.trans (by rw [identity,Submodule.map_id]))
  have replace := congrArg (fun A : TangentSpace (𝓘(ℝ,E)) (T x) →ₗ[ℝ] TangentSpace (𝓘(ℝ,E)) x =>
    (S (T x)).map A) back
  exact replace.symm.trans reverse

theorem map_inverse (T : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (K : Set M) (preserves : T '' K=K)
    (S : ∀ x, Submodule ℝ (TangentSpace (𝓘(ℝ,E)) x))
    (invariant : ∀ x ∈ K, (S x).map (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T x).toLinearMap=S (T x)) :
    ∀ x ∈ K, (S x).map (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm x).toLinearMap=S (T.symm x) := by
  intro x hx
  rw [←preserves] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  have target (z : M) (same : z=y) : S y=S z := by
    subst z
    rfl
  exact (inverse_at_image T forward inverse S y (invariant y hy)).trans
    (target _ (T.symm_apply_apply y))

end LeanShared.InvariantTangentDistributionIterates
