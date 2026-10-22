module
public import LeanShared.Analysis.EndpointJacobianComparison

/-! Jacobian comparison for actual unstable, stable-preimage and leaf tangent
subspaces. Every auxiliary graph and endpoint section is constructed. -/
public noncomputable section
namespace LeanShared.TransverseSubspaceJacobian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem compare (U S W : Submodule ℝ E) (A : E ≃L[ℝ] E)
    (Q : E →L[ℝ] U)
    (stableDimension : Module.finrank ℝ S = Module.finrank ℝ Uᗮ)
    (leafDimension : Module.finrank ℝ W = Module.finrank ℝ U)
    (stable : ∀ v : S, Q (A v) = 0)
    {LS LD M : ℝ} (stableNonnegative : 0 ≤ LS)
    (leafNonnegative : 0 ≤ LD) (imageNonnegative : 0 ≤ M)
    (stableSlope : ∀ v : S, ‖U.orthogonalProjectionOnto (v : E)‖ ≤
      LS * ‖Uᗮ.orthogonalProjectionOnto (v : E)‖)
    (leafSlope : ∀ v : W, ‖Uᗮ.orthogonalProjectionOnto (v : E)‖ ≤
      LD * ‖U.orthogonalProjectionOnto (v : E)‖)
    (imageTransverse : ∀ v : (A.toContinuousLinearMap.comp U.subtypeL).toLinearMap.range,
      ‖(v : E)‖ ≤ M * ‖Q v‖)
    (small : LS * LD < 1) :
    (A.toLinearMap.domRestrict U).normDet ≤
      (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) M *
        GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - LS * LD)) *
        (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) ‖Q‖ *
          GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) LD)) *
      (A.toLinearMap.domRestrict W).normDet := by
  obtain ⟨D, bound, range⟩ := BoundedProjectionGraph.exists_graph U W
    leafDimension leafNonnegative leafSlope
  have result := EndpointJacobianComparison.tangent_le U S A Q D stableDimension stable
    stableNonnegative imageNonnegative stableSlope imageTransverse bound small
  subst W
  exact result
end LeanShared.TransverseSubspaceJacobian
