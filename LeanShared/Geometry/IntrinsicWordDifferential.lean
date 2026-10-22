module

public import LeanShared.Geometry.DiffeomorphismDifferential
public import LeanShared.Analysis.IntrinsicPrincipalDensity
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! The chain-rule product in the intrinsic principal density is the actual
tangent derivative of the chronological word of diffeomorphisms. -/

@[expose] public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.IntrinsicWordDifferential
variable {E M G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  (F : G → M ≃ₜ M)
  (hF : ∀ a, MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (F a))
  (hi : ∀ a, MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (F a).symm)

include hF in
omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem orbit_mdifferentiable (word : List G) :
    MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (IntrinsicPrincipalDensity.orbit (fun a => F a) word) := by
  induction word with
  | nil => exact mdifferentiable_id
  | cons a word ih => exact ih.comp (hF a)

omit [FiniteDimensional ℝ E] in
theorem derivative_apply (word : List G) (x : M) (v : TangentSpace (𝓘(ℝ, E)) x) :
    IntrinsicPrincipalDensity.derivative (fun a => F a)
      (fun x => TangentSpace (𝓘(ℝ, E)) x)
      (fun a => DiffeomorphismDifferential.differential (F a) (hF a) (hi a)) word x v =
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (IntrinsicPrincipalDensity.orbit (fun a => F a) word) x v := by
  induction word generalizing x with
  | nil =>
    change v = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (id : M → M) x v
    rw [mfderiv_id]
    rfl
  | cons a word ih =>
    change IntrinsicPrincipalDensity.derivative (fun a => F a)
      (fun x => TangentSpace (𝓘(ℝ, E)) x)
      (fun a => DiffeomorphismDifferential.differential (F a) (hF a) (hi a)) word (F a x)
      (DiffeomorphismDifferential.differential (F a) (hF a) (hi a) x v) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
        (IntrinsicPrincipalDensity.orbit (fun a => F a) word ∘ F a) x v
    rw [ih, DiffeomorphismDifferential.differential_apply,
      mfderiv_comp x (orbit_mdifferentiable F hF word (F a x)) (hF a x)]
    rfl

end LeanShared.IntrinsicWordDifferential
