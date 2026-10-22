module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! A nonlinear secant on a convex chart domain is exactly the image of its
source secant under a linear map in the same derivative-comparison ball.
This is stronger than an error estimate and permits robust cone conditions
to be applied to actual finite chords. -/
public noncomputable section
namespace LeanShared.NonlinearSecantLinearization
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The correction is an actual rank-one operator with no loss in the
uniform derivative-comparison radius. -/
theorem exists_linear_secant (f : E → F) (A : E →L[ℝ] F) (s : Set E)
    (convex : Convex ℝ s) {δ : ℝ} (nonnegative : 0 ≤ δ)
    (differentiable : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (comparison : ∀ x ∈ s, ‖fderiv ℝ f x - A‖ ≤ δ)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ∃ B : E →L[ℝ] F, ‖B - A‖ ≤ δ ∧ B (y - x) = f y - f x := by
  by_cases equal : y = x
  · exact ⟨A, by simpa using nonnegative, by simp [equal]⟩
  let z := y - x
  let e := f y - f x - A z
  have positive : 0 < ‖z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr equal)
  have error : ‖e‖ ≤ δ * ‖z‖ :=
    convex.norm_image_sub_le_of_norm_fderiv_le' differentiable comparison hx hy
  let R : E →L[ℝ] F := (‖z‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ e z
  have normR : ‖R‖ ≤ δ := by
    rw [show ‖R‖ = (‖z‖ ^ 2)⁻¹ * (‖e‖ * ‖z‖) by
      simp only [R, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (sq_nonneg ‖z‖),
        InnerProductSpace.norm_rankOne]]
    calc
      _ ≤ (‖z‖ ^ 2)⁻¹ * ((δ * ‖z‖) * ‖z‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right error (norm_nonneg z))
          (inv_nonneg.mpr (sq_nonneg ‖z‖))
      _ = δ := by field_simp
  have action : R z = e := by
    simp only [R, smul_apply, InnerProductSpace.rankOne_def,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      smul_smul, inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos positive)), one_smul]
  refine ⟨A + R, ?_, ?_⟩
  · simpa only [add_sub_cancel_left] using normR
  · rw [add_apply, action]
    dsimp only [e]
    abel
/-- In the actual invertible derivative neighborhood, the secant map is a
continuous linear equivalence, so inverse-adjoint cone operations apply. -/
theorem exists_equiv_secant [FiniteDimensional ℝ E]
    (f : E → E) (A : E ≃L[ℝ] E) (s : Set E) (convex : Convex ℝ s)
    {δ : ℝ} (nonnegative : 0 ≤ δ) (small : ‖A.symm.toContinuousLinearMap‖ * δ < 1)
    (differentiable : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (comparison : ∀ x ∈ s, ‖fderiv ℝ f x - A.toContinuousLinearMap‖ ≤ δ)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ∃ B : E ≃L[ℝ] E, ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ ≤ δ ∧
      B (y - x) = f y - f x := by
  obtain ⟨B, close, action⟩ := exists_linear_secant f A.toContinuousLinearMap s convex
    nonnegative differentiable comparison hx hy
  have injective : Function.Injective B := by
    intro v w equal
    have zeroB : B (v - w) = 0 := by rw [map_sub, equal, sub_self]
    have error : ‖A (v - w)‖ ≤ δ * ‖v - w‖ := by
      calc
        _ = ‖(A.toContinuousLinearMap - B) (v - w)‖ := by
          rw [sub_apply, zeroB, sub_zero]
          rfl
        _ ≤ ‖A.toContinuousLinearMap - B‖ * ‖v - w‖ := (A.toContinuousLinearMap - B).le_opNorm _
        _ ≤ δ * ‖v - w‖ := mul_le_mul_of_nonneg_right
          ((norm_sub_rev _ _).trans_le close) (norm_nonneg _)
    have lower : ‖v - w‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A (v - w)‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
        using A.symm.toContinuousLinearMap.le_opNorm (A (v - w))
    have contract := lower.trans (mul_le_mul_of_nonneg_left error (norm_nonneg _))
    have zero : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp zero)
  let e := (LinearEquiv.ofInjectiveEndo B.toLinearMap injective).toContinuousLinearEquiv
  refine ⟨e, ?_, ?_⟩
  · have same : e.toContinuousLinearMap = B := by
      apply ContinuousLinearMap.ext
      intro z
      rfl
    rwa [same]
  · exact action
end LeanShared.NonlinearSecantLinearization
