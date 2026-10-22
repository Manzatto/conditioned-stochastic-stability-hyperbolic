module
public import LeanShared.Analysis.CompactCenteredDerivativeBound
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-! Uniform nonlinear radii in arbitrary bounded linear frames. The frames
need not vary continuously. Only the actual C¹ map and the compact set of
centers enter the radius, together with genuine bounds on frame operators. -/
public noncomputable section
namespace LeanShared.BoundedFrameNonlinearRadius
open Set
open LeanShared.CenteredManifoldCoordinates

private theorem derivative_at
    {P Q E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F) (a : E) (b : F) (h : E → F)
    (z : P) (smooth : DifferentiableAt ℝ h (a + L z)) :
    fderiv ℝ (centered L R a b h) z = R.symm.toContinuousLinearMap.comp
      ((fderiv ℝ h (a + L z)).comp L.toContinuousLinearMap) := by
  have source : HasFDerivAt (fun v : P => a + L v) L.toContinuousLinearMap z := by
    simpa only [zero_add] using (L.hasFDerivAt :
      HasFDerivAt L L.toContinuousLinearMap z).const_add a
  exact (R.symm.hasFDerivAt.comp z ((smooth.hasFDerivAt.comp z source).sub_const b)).fderiv

theorem exists_uniform_radius
    {P Q E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set E) (compact : IsCompact K) (h : E → F)
    (smooth : ∀ a ∈ K, ContDiffAt ℝ 1 h a)
    (C ε : ℝ) (positiveC : 0 < C) (positiveε : 0 < ε) :
    ∃ r > 0, ∀ a ∈ K, ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F),
      ‖L.toContinuousLinearMap‖ ≤ C → ‖R.symm.toContinuousLinearMap‖ ≤ C →
      ∀ b : F, ∀ z : P, ‖z‖ ≤ r →
        DifferentiableAt ℝ (centered L R a b h) z ∧
        ‖fderiv ℝ (centered L R a b h) z -
          fderiv ℝ (centered L R a b h) 0‖ < ε := by
  obtain ⟨δ, positiveδ, small⟩ := CompactCenteredDerivativeBound.exists_uniform_radius
    K compact h smooth (ε / (C * C)) (div_pos positiveε (mul_pos positiveC positiveC))
  refine ⟨δ / C, div_pos positiveδ positiveC, fun a ha L R boundL boundR b z hz => ?_⟩
  have displacement : ‖L z‖ ≤ δ := calc
    ‖L z‖ ≤ ‖L.toContinuousLinearMap‖ * ‖z‖ := L.toContinuousLinearMap.le_opNorm z
    _ ≤ C * ‖z‖ := mul_le_mul_of_nonneg_right boundL (norm_nonneg z)
    _ ≤ C * (δ / C) := mul_le_mul_of_nonneg_left hz positiveC.le
    _ = δ := by field_simp
  have local_data := small a ha (L z) displacement
  have at_z := (local_data.1.differentiableAt (by norm_num))
  have at_zero := (smooth a ha).differentiableAt (by norm_num)
  have zero_derivative : fderiv ℝ (centered L R a b h) 0 =
      R.symm.toContinuousLinearMap.comp ((fderiv ℝ h a).comp L.toContinuousLinearMap) := by
    simpa only [_root_.map_zero, add_zero] using derivative_at L R a b h 0
      (by simpa only [_root_.map_zero, add_zero] using at_zero)
  have derivative := derivative_at L R a b h z at_z
  refine ⟨?_, ?_⟩
  · have source : DifferentiableAt ℝ (fun v : P => a + L v) z :=
      L.differentiableAt.const_add a
    exact R.symm.differentiableAt.comp z ((at_z.comp z source).sub_const b)
  · rw [derivative, zero_derivative, ← ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.sub_comp]
    calc
      ‖R.symm.toContinuousLinearMap.comp
        ((fderiv ℝ h (a + L z) - fderiv ℝ h a).comp L.toContinuousLinearMap)‖
        ≤ ‖R.symm.toContinuousLinearMap‖ *
          (‖fderiv ℝ h (a + L z) - fderiv ℝ h a‖ * ‖L.toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _))
      _ ≤ C * (‖fderiv ℝ h (a + L z) - fderiv ℝ h a‖ * C) := by
        gcongr
      _ < C * ((ε / (C * C)) * C) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right local_data.2 positiveC) positiveC
      _ = ε := by field_simp

end LeanShared.BoundedFrameNonlinearRadius
