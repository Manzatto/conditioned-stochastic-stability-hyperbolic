module
public import LeanShared.Analysis.GraphPreimageJacobianComparison

/-! Endpoint projections need not be orthogonal, and source/target bundles
need not coincide. The constant uses only the actual projection and section
bounds, plus the stable-preimage graph angle. -/
public noncomputable section
namespace LeanShared.TransverseGraphJacobianComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem tangent_le (U : Submodule ℝ E) (D : U →L[ℝ] Uᗮ)
    (J : Uᗮ →L[ℝ] U) (A : E ≃L[ℝ] E)
    (Q : E →L[ℝ] U) (R : U →L[ℝ] E)
    (stable : ∀ v : Uᗮ, Q (A ((J v : E) + (v : E))) = 0)
    (factorization : A.toContinuousLinearMap.comp U.subtypeL =
      R.comp (Q.comp (A.toContinuousLinearMap.comp U.subtypeL)))
    {κ L C : ℝ} (small : κ < 1) (interaction : ‖J.comp D‖ ≤ κ)
    (slope : ‖D‖ ≤ L) (sectionBound : R.toLinearMap.normDet ≤ C) :
    (A.toLinearMap.domRestrict U).normDet ≤
      (C * GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - κ)) *
        (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) ‖Q‖ *
          GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) L)) *
      (A.toLinearMap.domRestrict
        (IntrinsicGraphJacobian.graphDifferential U D).toLinearMap.range).normDet := by
  let P := Q.comp (A.toContinuousLinearMap.comp U.subtypeL)
  let K := Q.comp (A.toContinuousLinearMap.comp (IntrinsicGraphJacobian.graphDifferential U D))
  have nonnegative : 0 ≤ C := (LinearMap.normDet_nonneg _).trans sectionBound
  have chain : (A.toLinearMap.domRestrict U).normDet = R.toLinearMap.normDet * |P.det| := by
    have equal := congrArg ContinuousLinearMap.toLinearMap factorization
    change A.toLinearMap.domRestrict U = R.toLinearMap.comp P.toLinearMap at equal
    rw [equal, LinearMap.normDet_comp_of_finrank_eq _ _ rfl, LinearMap.normDet_eq_abs_det]
  have projected := GraphPreimageJacobianComparison.projected_block_le
    U D J A.toContinuousLinearMap Q stable small interaction
  have tangent := RectangularJacobianBounds.graph_projected_determinant_le U D A Q slope
  rw [chain]
  calc
    _ ≤ C * (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - κ)) *
      |K.det|) := mul_le_mul sectionBound projected (abs_nonneg _) nonnegative
    _ ≤ C * (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - κ)) *
      ((GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) ‖Q‖ *
        GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) L) *
        (A.toLinearMap.domRestrict
          (IntrinsicGraphJacobian.graphDifferential U D).toLinearMap.range).normDet)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left tangent
        (GraphJacobian.densityBound_nonneg _)) nonnegative
    _ = _ := by ring
end LeanShared.TransverseGraphJacobianComparison
