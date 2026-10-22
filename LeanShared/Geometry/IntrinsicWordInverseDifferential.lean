module

public import LeanShared.Geometry.IntrinsicWordDifferential

/-! Actual inverse differentials for chronological diffeomorphism words. -/

@[expose] public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.IntrinsicWordDifferential

variable {E M G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  (F : G → M ≃ₜ M)
  (hF : ∀ a, MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (F a))
  (hi : ∀ a, MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (F a).symm)

/-- The actual homeomorphism composed in chronological word order. -/
def wordHomeomorph : List G → M ≃ₜ M
  | [] => Homeomorph.refl M
  | a :: word => (F a).trans (wordHomeomorph word)

@[simp] theorem wordHomeomorph_apply (word : List G) (x : M) :
    wordHomeomorph F word x = IntrinsicPrincipalDensity.orbit (fun a => F a) word x := by
  induction word generalizing x with
  | nil => rfl
  | cons a word ih => exact ih (F a x)

include hF in
omit [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem wordHomeomorph_mdifferentiable (word : List G) :
    MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (wordHomeomorph F word) := by
  induction word with
  | nil => exact mdifferentiable_id
  | cons a word ih => exact ih.comp (hF a)

include hi in
omit [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem wordHomeomorph_symm_mdifferentiable (word : List G) :
    MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (wordHomeomorph F word).symm := by
  induction word with
  | nil => exact mdifferentiable_id
  | cons a word ih => exact (hi a).comp ih

/-- Inverse of the genuine word differential, expressed through the actual
backward homeomorphism; equality of norms avoids artificial chart transports. -/
theorem norm_inverse_derivative (word : List G) (x : M)
    (v : TangentSpace (𝓘(ℝ, E)) (IntrinsicPrincipalDensity.orbit (fun a => F a) word x)) :
    ‖(IntrinsicPrincipalDensity.derivative (fun a => F a)
      (fun x => TangentSpace (𝓘(ℝ, E)) x)
      (fun a => DiffeomorphismDifferential.differential (F a) (hF a) (hi a)) word x).symm v‖ =
    ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (wordHomeomorph F word).symm
      (IntrinsicPrincipalDensity.orbit (fun a => F a) word x) v‖ := by
  let A := DiffeomorphismDifferential.differential (wordHomeomorph F word)
    (wordHomeomorph_mdifferentiable F hF word)
    (wordHomeomorph_symm_mdifferentiable F hi word) x
  have hEq : (wordHomeomorph F word : M → M) = IntrinsicPrincipalDensity.orbit (fun a => F a) word :=
    funext (wordHomeomorph_apply F word)
  have heq : ∀ w : TangentSpace (𝓘(ℝ, E)) x,
      A w = IntrinsicPrincipalDensity.derivative (fun a => F a)
        (fun x => TangentSpace (𝓘(ℝ, E)) x)
        (fun a => DiffeomorphismDifferential.differential (F a) (hF a) (hi a)) word x w := by
    intro w
    rw [derivative_apply F hF hi]
    change mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (wordHomeomorph F word) x w = _
    rw [hEq]
  let B := IntrinsicPrincipalDensity.derivative (fun a => F a)
    (fun x => TangentSpace (𝓘(ℝ, E)) x)
    (fun a => DiffeomorphismDifferential.differential (F a) (hF a) (hi a)) word x
  have hv : B.symm v = A.symm v := by
    apply A.injective
    have h1 : (A (B.symm v) : E) = (v : E) :=
      (heq (B.symm v)).trans (B.apply_symm_apply v)
    exact h1.trans (A.apply_symm_apply v).symm
  have hraw : A.symm v =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (wordHomeomorph F word).symm
        (wordHomeomorph F word x) v := rfl
  have hpoint : (wordHomeomorph F word).symm
      (IntrinsicPrincipalDensity.orbit (fun a => F a) word x) = x := by
    rw [← wordHomeomorph_apply]
    exact (wordHomeomorph F word).symm_apply_apply x
  have hn : ‖(show TangentSpace (𝓘(ℝ, E)) x from
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (wordHomeomorph F word).symm
        (IntrinsicPrincipalDensity.orbit (fun a => F a) word x) v)‖ =
      ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (wordHomeomorph F word).symm
        (IntrinsicPrincipalDensity.orbit (fun a => F a) word x) v‖ := by
    exact congrArg (fun q : Norm E => @norm E q
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (wordHomeomorph F word).symm
        (IntrinsicPrincipalDensity.orbit (fun a => F a) word x) v))
      (congrArg (fun y : M => (show Norm E from (inferInstance : NormedAddCommGroup (TangentSpace (𝓘(ℝ, E)) y)).toNorm)) hpoint).symm
  apply Eq.trans _ hn
  apply congrArg (fun w : TangentSpace (𝓘(ℝ, E)) x => ‖w‖)
  exact hv.trans (hraw.trans (congrArg
    (fun y => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (wordHomeomorph F word).symm y v)
    (wordHomeomorph_apply F word x)))

end LeanShared.IntrinsicWordDifferential
