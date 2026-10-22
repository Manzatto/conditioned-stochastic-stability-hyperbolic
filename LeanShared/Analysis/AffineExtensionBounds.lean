module
public import LeanShared.Analysis.SmallAffinePerturbation

/-! Quantitative bounds for an actual globally defined affine extension.
The inverse estimates use the actual derivative margin and the actual
linear inverse; affine agreement also gives a compact inverse correction. -/
@[expose] public noncomputable section
open Set Function
open scoped NNReal Topology
namespace LeanShared.AffineExtensionBounds
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem derivative_norm_le (H : E → F) (A : E →L[ℝ] F) {K ε : ℝ}
    (prototype : ‖A‖ ≤ K) (close : ∀ x, ‖fderiv ℝ H x-A‖ ≤ ε) :
    ∀ x, ‖fderiv ℝ H x‖ ≤ K+ε := by
  intro x
  calc
    _ ≤ ‖fderiv ℝ H x-A‖+‖A‖ := norm_le_norm_sub_add _ _
    _ ≤ ε+K := add_le_add (close x) prototype
    _ = K+ε := add_comm _ _

theorem inverse_lipschitz (H : E ≃ₜ F) (A : E ≃L[ℝ] F)
    (smooth : Differentiable ℝ H) {K ε : ℝ} (nonnegativeK : 0 ≤ K)
    (nonnegativeε : 0 ≤ ε) (prototype : ‖A.symm.toContinuousLinearMap‖ ≤ K)
    (small : K*ε < 1) (close : ∀ x, ‖fderiv ℝ H x-A.toContinuousLinearMap‖ ≤ ε) :
    LipschitzWith ⟨K/(1-K*ε), div_nonneg nonnegativeK (by linarith)⟩ H.symm := by
  let u : E → F := fun x => H x-A x
  have du : Differentiable ℝ u := smooth.sub A.differentiable
  have derivative (x : E) : ‖fderiv ℝ u x‖ ≤ (⟨ε, nonnegativeε⟩ : ℝ≥0) := by
    have actual : HasFDerivAt u (fderiv ℝ H x-A.toContinuousLinearMap) x :=
      (smooth x).hasFDerivAt.sub A.hasFDerivAt
    rw [actual.fderiv]
    exact close x
  have lip := SmallAffinePerturbation.lipschitz_of_derivative du derivative
  apply LipschitzWith.of_dist_le_mul
  intro y z
  let v : E := H.symm y-H.symm z
  have linearLower : ‖v‖ ≤ K*‖A v‖ := by
    calc
      ‖v‖ = ‖A.symm (A v)‖ := by rw [A.symm_apply_apply]
      _ ≤ ‖A.symm.toContinuousLinearMap‖*‖A v‖ := A.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ K*‖A v‖ := mul_le_mul_of_nonneg_right prototype (norm_nonneg _)
  have identity : A v = y-z-(u (H.symm y)-u (H.symm z)) := by
    dsimp only [v, u]
    simp only [map_sub, H.apply_symm_apply]
    abel
  have residual : ‖A v‖ ≤ ‖y-z‖+ε*‖v‖ := by
    rw [identity]
    exact (norm_sub_le _ _).trans
      (add_le_add (le_refl ‖y-z‖) (lip.norm_sub_le (H.symm y) (H.symm z)))
  have lower := linearLower.trans (mul_le_mul_of_nonneg_left residual nonnegativeK)
  have divide : ‖v‖ ≤ (K*‖y-z‖)/(1-K*ε) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-K*ε)).mpr
    nlinarith [lower]
  rw [dist_eq_norm, dist_eq_norm]
  change ‖H.symm y-H.symm z‖ ≤ (K/(1-K*ε))*‖y-z‖
  simpa only [v, div_mul_eq_mul_div] using divide

theorem inverse_derivative_norm_le (H : E ≃ₜ F) (A : E ≃L[ℝ] F)
    (smooth : Differentiable ℝ H) {K ε : ℝ} (nonnegativeK : 0 ≤ K)
    (nonnegativeε : 0 ≤ ε) (prototype : ‖A.symm.toContinuousLinearMap‖ ≤ K)
    (small : K*ε < 1) (close : ∀ x, ‖fderiv ℝ H x-A.toContinuousLinearMap‖ ≤ ε) :
    ∀ y, ‖fderiv ℝ H.symm y‖ ≤ K/(1-K*ε) := by
  intro y
  exact norm_fderiv_le_of_lipschitz ℝ
    (inverse_lipschitz H A smooth nonnegativeK nonnegativeε prototype small close)

/-- A half-margin yields one common inverse Lipschitz and derivative
bound for the entire family, including zero-dimensional models. -/
theorem inverse_uniform_bounds (H : E ≃ₜ F) (A : E ≃L[ℝ] F)
    (smooth : Differentiable ℝ H) {K ε : ℝ} (nonnegativeK : 0 ≤ K)
    (nonnegativeε : 0 ≤ ε) (prototype : ‖A.symm.toContinuousLinearMap‖ ≤ K)
    (small : K*ε ≤ 1/2) (close : ∀ x, ‖fderiv ℝ H x-A.toContinuousLinearMap‖ ≤ ε) :
    LipschitzWith ⟨2*K, by positivity⟩ H.symm ∧
      ∀ y, ‖fderiv ℝ H.symm y‖ ≤ 2*K := by
  have strict : K*ε < 1 := small.trans_lt (by norm_num)
  have denominator : 0 < 1-K*ε := by linarith
  have scaled := mul_le_mul_of_nonneg_left small nonnegativeK
  have fraction : K/(1-K*ε) ≤ 2*K := by
    apply (div_le_iff₀ denominator).mpr
    nlinarith [scaled]
  have lip := inverse_lipschitz H A smooth nonnegativeK nonnegativeε prototype strict close
  have uniform : LipschitzWith ⟨2*K, by positivity⟩ H.symm :=
    lip.weaken (by exact_mod_cast fraction)
  exact ⟨uniform, fun _ => norm_fderiv_le_of_lipschitz ℝ uniform⟩

theorem inverse_eq_affine_off_image (H : E ≃ₜ F) (A : E ≃L[ℝ] F) (b : F)
    {S : Set E} (agreement : ∀ x, x ∉ S → H x = A x+b) (y : F)
    (outside : y ∉ (fun x => A x+b) '' S) : H.symm y = A.symm (y-b) := by
  have absent : A.symm (y-b) ∉ S := by
    intro member
    apply outside
    exact ⟨A.symm (y-b), member, by simp only [A.apply_symm_apply, sub_add_cancel]⟩
  apply H.injective
  rw [H.apply_symm_apply, agreement _ absent]
  simp only [A.apply_symm_apply, sub_add_cancel]

theorem hasCompactSupport_inverse_correction (H : E ≃ₜ F) (A : E ≃L[ℝ] F) (b : F)
    {S : Set E} (compact : IsCompact S) (agreement : ∀ x, x ∉ S → H x = A x+b) :
    HasCompactSupport (fun y => H.symm y-A.symm (y-b)) := by
  have compactImage : IsCompact ((fun x => A x+b) '' S) :=
    compact.image (A.continuous.add continuous_const)
  apply compactImage.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ compactImage.isClosed
  intro y hy
  by_contra outside
  exact hy (sub_eq_zero.mpr (inverse_eq_affine_off_image H A b agreement y outside))

end LeanShared.AffineExtensionBounds
