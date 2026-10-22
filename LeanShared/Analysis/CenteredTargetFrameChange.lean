module
public import LeanShared.Analysis.CenteredOffsetChange
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Tactic.Linarith

/-! Exact target-frame changes and their derivative error. The reference
offset is arbitrary; the linear comparison uses the actual two frames. -/
public noncomputable section
namespace LeanShared.CenteredManifoldCoordinates
variable {P Q E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_centered_target_frame (L : P ≃L[ℝ] E) (R S : Q ≃L[ℝ] F)
    (a : E) (b c : F) (h : E → F) (z : P) :
    fderiv ℝ (centered L S a c h) z =
      (S.symm.toContinuousLinearMap.comp R.toContinuousLinearMap).comp
        (fderiv ℝ (centered L R a b h) z) := by
  rw [fderiv_centered_offset L S a c b]
  have identity : centered L S a b h =
      (R.trans S.symm) ∘ centered L R a b h := by
    funext v
    simp only [centered, Function.comp_apply, ContinuousLinearEquiv.trans_apply,
      R.apply_symm_apply]
  rw [identity, ContinuousLinearEquiv.comp_fderiv]
  rfl

theorem target_frame_derivative_error (L : P ≃L[ℝ] E) (R S : Q ≃L[ℝ] F)
    (a : E) (b c : F) (h : E → F) (z : P) (D : P →L[ℝ] Q)
    (η ε B : ℝ)
    (relative : ‖S.symm.toContinuousLinearMap.comp R.toContinuousLinearMap -
      ContinuousLinearMap.id ℝ Q‖ ≤ η)
    (near : ‖fderiv ℝ (centered L R a b h) z - D‖ ≤ ε)
    (bound : ‖D‖ ≤ B) :
    ‖fderiv ℝ (centered L S a c h) z - D‖ ≤ (1 + η) * ε + η * B := by
  let A := S.symm.toContinuousLinearMap.comp R.toContinuousLinearMap
  let V := fderiv ℝ (centered L R a b h) z
  have nonnegativeη : 0 ≤ η := (norm_nonneg _).trans relative
  have nonnegativeε : 0 ≤ ε := (norm_nonneg _).trans near
  have normA : ‖A‖ ≤ 1 + η := by
    have triangle := norm_add_le (A - ContinuousLinearMap.id ℝ Q)
      (ContinuousLinearMap.id ℝ Q)
    rw [sub_add_cancel] at triangle
    exact triangle.trans (by
      have idBound := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Q)
      dsimp only [A] at *
      linarith)
  rw [fderiv_centered_target_frame]
  have identity : A.comp V - D = A.comp (V - D) +
      (A - ContinuousLinearMap.id ℝ Q).comp D := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.id_comp]
    abel
  change ‖A.comp V - D‖ ≤ _
  rw [identity]
  calc
    _ ≤ ‖A.comp (V - D)‖ + ‖(A - ContinuousLinearMap.id ℝ Q).comp D‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖V - D‖ + ‖A - ContinuousLinearMap.id ℝ Q‖ * ‖D‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (1 + η) * ε + η * B := add_le_add
      (mul_le_mul normA near (norm_nonneg _) (by positivity))
      (mul_le_mul relative bound (norm_nonneg _) nonnegativeη)

end LeanShared.CenteredManifoldCoordinates
