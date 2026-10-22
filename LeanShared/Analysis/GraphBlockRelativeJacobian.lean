module

public import LeanShared.Analysis.GraphBlockPerturbation
public import LeanShared.Geometry.RelativeDeterminantPerturbation

/-! For any prescribed loss γ>1, one uniform small block perturbation
bounds every unstable-graph principal Jacobian by γ times the reference
unstable determinant. The radius is constructed from determinant continuity. -/
public noncomputable section
namespace LeanShared.GraphBlockRelativeJacobian
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem exists_radius (γ : ℝ) (hγ : 1 < γ) :
    ∃ η : ℝ, 0 < η ∧ ∀ A : U ≃L[ℝ] U, ∀ B : S →L[ℝ] S,
      ∀ L : U × S →L[ℝ] U × S, ∀ G : U →L[ℝ] S,
      ‖A.symm.toContinuousLinearMap‖ ≤ 1 → ‖G‖ ≤ 1 →
      ‖L - A.toContinuousLinearMap.prodMap B‖ ≤ η →
      |(GraphBlockPerturbation.upper L G).det| ≤ γ * |A.toContinuousLinearMap.det| := by
  obtain ⟨η, positive, determinant⟩ := RelativeDeterminantPerturbation.exists_radius (E := U) γ hγ
  refine ⟨η, positive, fun A B L G hA hG close => ?_⟩
  apply determinant A (GraphBlockPerturbation.upper L G)
  calc
    _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖GraphBlockPerturbation.upper L G - A.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * η := mul_le_mul hA (GraphBlockPerturbation.upper_error _ B L G hG η close)
      (norm_nonneg _) zero_le_one
    _ = η := one_mul _

end LeanShared.GraphBlockRelativeJacobian
