module
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Normed.Operator.Banach

/-! The actual derivatives of a differentiable homeomorphism and its
actual differentiable inverse form a continuous linear equivalence. -/
public noncomputable section
namespace LeanShared.HomeomorphDerivativeEquivalence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverse_comp (H : E ≃ₜ E) (smooth : Differentiable ℝ H)
    (inverseSmooth : Differentiable ℝ H.symm) (x : E) :
    (fderiv ℝ H.symm (H x)).comp (fderiv ℝ H x) = ContinuousLinearMap.id ℝ E := by
  exact ((inverseSmooth (H x)).hasFDerivAt.comp x (smooth x).hasFDerivAt).unique
    ((hasFDerivAt_id x).congr_of_eventuallyEq (Filter.Eventually.of_forall H.symm_apply_apply))

theorem comp_inverse (H : E ≃ₜ E) (smooth : Differentiable ℝ H)
    (inverseSmooth : Differentiable ℝ H.symm) (x : E) :
    (fderiv ℝ H x).comp (fderiv ℝ H.symm (H x)) = ContinuousLinearMap.id ℝ E := by
  simpa only [H.symm_apply_apply, Homeomorph.symm_symm] using inverse_comp H.symm inverseSmooth smooth (H x)

theorem bijective (H : E ≃ₜ E) (smooth : Differentiable ℝ H)
    (inverseSmooth : Differentiable ℝ H.symm) (x : E) :
    Function.Bijective (fderiv ℝ H x) := by
  have left (v : E) : fderiv ℝ H.symm (H x) (fderiv ℝ H x v) = v :=
    congrArg (fun A : E →L[ℝ] E => A v) (inverse_comp H smooth inverseSmooth x)
  have right (v : E) : fderiv ℝ H x (fderiv ℝ H.symm (H x) v) = v :=
    congrArg (fun A : E →L[ℝ] E => A v) (comp_inverse H smooth inverseSmooth x)
  exact ⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩

variable [CompleteSpace E]

@[expose] def derivative (H : E ≃ₜ E) (smooth : Differentiable ℝ H)
    (inverseSmooth : Differentiable ℝ H.symm) (x : E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ H x)
    (LinearMap.ker_eq_bot.mpr (bijective H smooth inverseSmooth x).1)
    (LinearMap.range_eq_top.mpr (bijective H smooth inverseSmooth x).2)

theorem derivative_coe (H : E ≃ₜ E) (smooth : Differentiable ℝ H)
    (inverseSmooth : Differentiable ℝ H.symm) (x : E) :
    (derivative H smooth inverseSmooth x).toContinuousLinearMap = fderiv ℝ H x := by
  simp only [derivative, ContinuousLinearEquiv.coe_ofBijective]

theorem inverse_derivative_coe (H : E ≃ₜ E) (smooth : Differentiable ℝ H)
    (inverseSmooth : Differentiable ℝ H.symm) (x : E) :
    (derivative H smooth inverseSmooth x).symm.toContinuousLinearMap = fderiv ℝ H.symm (H x) := by
  ext v
  apply (derivative H smooth inverseSmooth x).injective
  change (derivative H smooth inverseSmooth x)
    ((derivative H smooth inverseSmooth x).symm v) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change v = fderiv ℝ H x (fderiv ℝ H.symm (H x) v)
  exact (congrArg (fun A : E →L[ℝ] E => A v) (comp_inverse H smooth inverseSmooth x)).symm

end LeanShared.HomeomorphDerivativeEquivalence
