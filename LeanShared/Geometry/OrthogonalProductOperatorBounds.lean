module
public import LeanShared.Analysis.OrthogonalDiagonalInverseBound
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Tactic.Linarith

/-! Quantitative transport from actual max-product adapted coordinates to
a genuine Euclidean Hilbert model. The product norm is retained explicitly. -/
public noncomputable section
namespace LeanShared.OrthogonalProductCoordinates
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

theorem equiv_norm_le_two (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E) :
    ‖(equiv dimension).toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  exact (norm_le_axis_sum dimension z).trans (by
    nlinarith [norm_fst_le z, norm_snd_le z])

theorem inverse_equiv_norm_le_one (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E) :
    ‖(equiv dimension).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  obtain ⟨z, rfl⟩ := (equiv dimension).surjective v
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    one_mul, Prod.norm_def] using
    max_le (axis_norm_le dimension z).1 (axis_norm_le dimension z).2

theorem norm_sq (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E) (z : X × Y) :
    ‖equiv dimension z‖ ^ 2 = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_map dimension z z

@[expose] def transport (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (A : (X × Y) →L[ℝ] (X × Y)) : E →L[ℝ] E :=
  (equiv dimension).toContinuousLinearMap.comp
    (A.comp (equiv dimension).symm.toContinuousLinearMap)

theorem transport_norm_le (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (A : (X × Y) →L[ℝ] (X × Y)) : ‖transport dimension A‖ ≤ 2 * ‖A‖ := by
  calc
    _ ≤ ‖(equiv dimension).toContinuousLinearMap‖ *
        (‖A‖ * ‖(equiv dimension).symm.toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg (equiv dimension).toContinuousLinearMap))
    _ ≤ 2 * (‖A‖ * 1) := mul_le_mul (equiv_norm_le_two dimension)
      (mul_le_mul_of_nonneg_left (inverse_equiv_norm_le_one dimension) (norm_nonneg A))
      (mul_nonneg (norm_nonneg A) (norm_nonneg (equiv dimension).symm.toContinuousLinearMap)) (by norm_num)
    _ = 2 * ‖A‖ := by rw [mul_one]

theorem transport_sub (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (A B : (X × Y) →L[ℝ] (X × Y)) :
    transport dimension (A - B) = transport dimension A - transport dimension B := by
  simp only [transport, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

theorem transported_fderiv (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (f : X × Y → X × Y) (v : E) :
    fderiv ℝ (equiv dimension ∘ f ∘ (equiv dimension).symm) v =
      transport dimension (fderiv ℝ f ((equiv dimension).symm v)) := by
  rw [ContinuousLinearEquiv.comp_fderiv, ContinuousLinearEquiv.comp_right_fderiv]
  rfl

end LeanShared.OrthogonalProductCoordinates
