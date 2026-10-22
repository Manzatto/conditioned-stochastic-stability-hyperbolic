module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Noise derivatives of an actual inverse family

The chain rule differentiates `F (ω, G (ω,y)) = y`. Invertibility of the
spatial derivative then determines the inverse noise derivative and proves
that noise submersivity is preserved. Differentiability of the inverse
family remains an explicit classical input, rather than its derivative
formula or the resulting submersivity.
-/

@[expose] public noncomputable section

open Filter Function
open scoped Topology

namespace LeanShared.ParametricInverseDerivative

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Solve the differentiated inverse identity in continuous linear maps. -/
theorem solve_inverse_derivative (A : E ≃L[ℝ] E) (B D : P →L[ℝ] E)
    (h : B + (A : E →L[ℝ] E).comp D = 0) :
    D = -((A.symm : E →L[ℝ] E).comp B) := by
  apply ContinuousLinearMap.ext
  intro v
  change D v = -(A.symm (B v))
  apply eq_neg_iff_add_eq_zero.mpr
  have hz : B v + A (D v) = 0 := by
    simpa using congrArg (fun L : P →L[ℝ] E => L v) h
  have hh := congrArg A.symm hz
  simpa only [map_add, map_zero, A.symm_apply_apply, add_comm] using hh

/-- An invertible spatial factor and a sign preserve surjectivity. -/
theorem inverse_derivative_surjective (A : E ≃L[ℝ] E) (B D : P →L[ℝ] E)
    (h : B + (A : E →L[ℝ] E).comp D = 0) (hB : Surjective B) : Surjective D := by
  rw [solve_inverse_derivative A B D h]
  intro y
  obtain ⟨v, hv⟩ := hB (-(A y))
  refine ⟨v, ?_⟩
  change -(A.symm (B v)) = y
  rw [hv, map_neg, A.symm_apply_apply, neg_neg]

/-- The actual chain rule supplies the linear identity, using only local
agreement with the inverse equation around the parameter. -/
theorem differentiated_inverse_identity (F G : P × E → E) (ω : P) (y : E)
    (A : E ≃L[ℝ] E) (B D : P →L[ℝ] E)
    (hF : HasFDerivAt F (B.coprod (A : E →L[ℝ] E)) (ω, G (ω, y)))
    (hG : HasFDerivAt (fun p => G (p, y)) D ω)
    (hidentity : ∀ᶠ p in 𝓝 ω, F (p, G (p, y)) = y) :
    B + (A : E →L[ℝ] E).comp D = 0 := by
  have hc := hF.comp ω ((hasFDerivAt_id ω).prodMk hG)
  have hz : HasFDerivAt (fun p => F (p, G (p, y))) (0 : P →L[ℝ] E) ω :=
    (hasFDerivAt_const y ω).congr_of_eventuallyEq hidentity
  have he := hc.unique hz
  calc
    B + (A : E →L[ℝ] E).comp D =
        (B.coprod (A : E →L[ℝ] E)).comp ((ContinuousLinearMap.id ℝ P).prod D) := by
      apply ContinuousLinearMap.ext
      intro v
      rfl
    _ = 0 := he

/-- The literal inverse noise derivative has the claimed formula. -/
theorem fderiv_noise_inverse_eq (F G : P × E → E) (ω : P) (y : E)
    (A : E ≃L[ℝ] E) (B : P →L[ℝ] E)
    (hF : HasFDerivAt F (B.coprod (A : E →L[ℝ] E)) (ω, G (ω, y)))
    (hG : DifferentiableAt ℝ (fun p => G (p, y)) ω)
    (hidentity : ∀ᶠ p in 𝓝 ω, F (p, G (p, y)) = y) :
    fderiv ℝ (fun p => G (p, y)) ω = -((A.symm : E →L[ℝ] E).comp B) :=
  solve_inverse_derivative A B _ (differentiated_inverse_identity F G ω y A B _ hF hG.hasFDerivAt hidentity)

/-- Noise submersivity of the forward family implies noise submersivity
of the actual inverse family. -/
theorem fderiv_noise_inverse_surjective (F G : P × E → E) (ω : P) (y : E)
    (A : E ≃L[ℝ] E) (B : P →L[ℝ] E)
    (hF : HasFDerivAt F (B.coprod (A : E →L[ℝ] E)) (ω, G (ω, y)))
    (hG : DifferentiableAt ℝ (fun p => G (p, y)) ω)
    (hidentity : ∀ᶠ p in 𝓝 ω, F (p, G (p, y)) = y) (hB : Surjective B) :
    Surjective (fderiv ℝ (fun p => G (p, y)) ω) :=
  inverse_derivative_surjective A B _
    (differentiated_inverse_identity F G ω y A B _ hF hG.hasFDerivAt hidentity) hB

/-- Joint differentiability and an actual spatial derivative identify the
joint derivative with the coprod of the literal noise derivative and the
spatial equivalence. No decomposition of that derivative is assumed. -/
theorem hasFDerivAt_coprod_of_partials (F : P × E → E) (ω : P) (x : E)
    (A : E ≃L[ℝ] E) (hF : DifferentiableAt ℝ F (ω, x))
    (hA : HasFDerivAt (fun z => F (ω, z)) (A : E →L[ℝ] E) x) :
    HasFDerivAt F ((fderiv ℝ (fun p => F (p, x)) ω).coprod (A : E →L[ℝ] E)) (ω, x) := by
  have hb : fderiv ℝ (fun p => F (p, x)) ω =
      (fderiv ℝ F (ω, x)).comp (ContinuousLinearMap.inl ℝ P E) :=
    (hF.hasFDerivAt.comp ω ((hasFDerivAt_id ω).prodMk (hasFDerivAt_const x ω))).fderiv
  have ha : (A : E →L[ℝ] E) =
      (fderiv ℝ F (ω, x)).comp (ContinuousLinearMap.inr ℝ P E) :=
    hA.unique (hF.hasFDerivAt.comp x ((hasFDerivAt_const ω x).prodMk (hasFDerivAt_id x)))
  rw [hb, ha, ContinuousLinearMap.coprod_comp_inl_inr]
  exact hF.hasFDerivAt

/-- Fully identified noise-submersion producer for the inverse family.
Both noise derivatives are literal `fderiv`s of the actual forward and
inverse maps. -/
theorem inverse_noise_submersion_of_partials (F G : P × E → E) (ω : P) (y : E)
    (A : E ≃L[ℝ] E) (hF : DifferentiableAt ℝ F (ω, G (ω, y)))
    (hA : HasFDerivAt (fun z => F (ω, z)) (A : E →L[ℝ] E) (G (ω, y)))
    (hG : DifferentiableAt ℝ (fun p => G (p, y)) ω)
    (hidentity : ∀ᶠ p in 𝓝 ω, F (p, G (p, y)) = y)
    (hB : Surjective (fderiv ℝ (fun p => F (p, G (ω, y))) ω)) :
    Surjective (fderiv ℝ (fun p => G (p, y)) ω) :=
  fderiv_noise_inverse_surjective F G ω y A _
    (hasFDerivAt_coprod_of_partials F ω (G (ω, y)) A hF hA) hG hidentity hB

end LeanShared.ParametricInverseDerivative
