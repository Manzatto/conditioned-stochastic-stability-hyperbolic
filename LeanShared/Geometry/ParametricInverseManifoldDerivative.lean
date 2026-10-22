module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! The inverse control derivative is surjective because the actual forward
control derivative is surjective. Joint differentiability of the inverse
family remains an ordinary calculus input; neither its derivative formula
nor its noise submersivity is assumed. -/

@[expose] public noncomputable section
open Function Filter
open scoped Manifold Topology
namespace LeanShared.ParametricInverseManifoldDerivative

section Algebra
variable {P E F : Type*} [AddCommGroup F]

theorem surjective_of_inverse_identity (A : E → F) (B : P → F)
    (D : P → E) (hA : Injective A) (hB : Surjective B)
    (h : ∀ v, B v + A (D v) = 0) : Surjective D := by
  intro y
  obtain ⟨v, hv⟩ := hB (-(A y))
  refine ⟨v, hA ?_⟩
  have hz := h v
  rw [hv] at hz
  exact (neg_add_eq_zero.mp hz).symm

end Algebra

variable {P E M : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Differentiate the actual local identity F(p,G(p,y))=y using the
manifold chain rule and the literal partial derivatives. -/
theorem differentiated_identity (F G : P × M → M) (ω : P) (y : M)
    (hF : MDifferentiableAt ((𝓘(ℝ, P)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) F (ω, G (ω, y)))
    (hG : MDifferentiableAt (𝓘(ℝ, P)) (𝓘(ℝ, E)) (fun p => G (p, y)) ω)
    (identity : ∀ᶠ p in 𝓝 ω, F (p, G (p, y)) = y) :
    mfderiv (𝓘(ℝ, P)) (𝓘(ℝ, E)) (fun p => F (p, G (ω, y))) ω +
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x => F (ω, x)) (G (ω, y))).comp
        (mfderiv (𝓘(ℝ, P)) (𝓘(ℝ, E)) (fun p => G (p, y)) ω) = 0 := by
  have chain := mfderiv_comp ω hF (mdifferentiableAt_id.prodMk hG)
  have zero : mfderiv (𝓘(ℝ, P)) (𝓘(ℝ, E)) (fun p => F (p, G (p, y))) ω = 0 := by
    have heq : (fun p => F (p, G (p, y))) =ᶠ[𝓝 ω] (fun _ => y) := identity
    rw [heq.mfderiv_eq (I := 𝓘(ℝ, P)) (I' := 𝓘(ℝ, E)), mfderiv_const]
    simp
  have product : mfderiv (𝓘(ℝ, P)) ((𝓘(ℝ, P)).prod (𝓘(ℝ, E)))
      (fun p => (p, G (p, y))) ω =
      (ContinuousLinearMap.id ℝ P).prod
        (mfderiv (𝓘(ℝ, P)) (𝓘(ℝ, E)) (fun p => G (p, y)) ω) := by
    have hid : mfderiv (𝓘(ℝ, P)) (𝓘(ℝ, P)) (id : P → P) ω =
        ContinuousLinearMap.id ℝ P := by
      exact mfderiv_id
    have hp := mfderiv_prodMk mdifferentiableAt_id hG
    rw [hid] at hp
    exact hp
  simp only [Function.id_def, Function.comp_def] at chain
  erw [product, mfderiv_prod_eq_add_comp hF] at chain
  rw [zero] at chain
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun L => L v) chain.symm
  exact h

/-- The inverse submersion condition is a deduction from forward noise
nondegeneracy and the ordinary spatial local-diffeomorphism condition. -/
theorem inverse_control_surjective (F G : P × M → M) (ω : P) (y : M)
    (hF : MDifferentiableAt ((𝓘(ℝ, P)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) F (ω, G (ω, y)))
    (hG : MDifferentiableAt (𝓘(ℝ, P)) (𝓘(ℝ, E)) (fun p => G (p, y)) ω)
    (identity : ∀ᶠ p in 𝓝 ω, F (p, G (p, y)) = y)
    (spatial : Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (fun x => F (ω, x)) (G (ω, y))))
    (noise : Surjective (mfderiv (𝓘(ℝ, P)) (𝓘(ℝ, E))
      (fun p => F (p, G (ω, y))) ω)) :
    Surjective (mfderiv (𝓘(ℝ, P)) (𝓘(ℝ, E)) (fun p => G (p, y)) ω) :=
  surjective_of_inverse_identity _ _ _ spatial noise
    (fun v => congrArg (fun L => L v)
      (differentiated_identity F G ω y hF hG identity))

end LeanShared.ParametricInverseManifoldDerivative
