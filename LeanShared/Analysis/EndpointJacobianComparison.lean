module
public import LeanShared.Analysis.EndpointGraphConstruction
public import LeanShared.Analysis.TransverseGraphJacobianComparison
public import LeanShared.Analysis.BoundedImageSection

/-! A word-independent Jacobian comparison built from actual endpoint
subspaces. The stable space is a preimage, not an invariant source bundle;
the endpoint projection may be oblique. -/
public noncomputable section
namespace LeanShared.EndpointJacobianComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem tangent_le (U S : Submodule ℝ E) (A : E ≃L[ℝ] E)
    (Q : E →L[ℝ] U) (D : U →L[ℝ] Uᗮ)
    (stableDimension : Module.finrank ℝ S = Module.finrank ℝ Uᗮ)
    (stable : ∀ v : S, Q (A v) = 0)
    {LS LD M : ℝ} (stableNonnegative : 0 ≤ LS) (imageNonnegative : 0 ≤ M)
    (stableSlope : ∀ v : S, ‖U.orthogonalProjectionOnto (v : E)‖ ≤
      LS * ‖Uᗮ.orthogonalProjectionOnto (v : E)‖)
    (imageTransverse : ∀ v : (A.toContinuousLinearMap.comp U.subtypeL).toLinearMap.range,
      ‖(v : E)‖ ≤ M * ‖Q v‖)
    (leafSlope : ‖D‖ ≤ LD) (small : LS * LD < 1) :
    (A.toLinearMap.domRestrict U).normDet ≤
      (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) M *
        GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - LS * LD)) *
        (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) ‖Q‖ *
          GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) LD)) *
      (A.toLinearMap.domRestrict
        (IntrinsicGraphJacobian.graphDifferential U D).toLinearMap.range).normDet := by
  obtain ⟨J, boundJ, graphJ⟩ := EndpointGraphConstruction.exists_preimage_graph
    U S stableDimension stableNonnegative stableSlope
  have annihilates (v : Uᗮ) : Q (A ((J v : E) + (v : E))) = 0 :=
    stable ⟨_, graphJ v⟩
  have interaction : ‖J.comp D‖ ≤ LS * LD := by
    exact (ContinuousLinearMap.opNorm_comp_le J D).trans
      (mul_le_mul boundJ leafSlope (norm_nonneg _) stableNonnegative)
  let B := A.toContinuousLinearMap.comp U.subtypeL
  have injective : Function.Injective B := A.injective.comp Subtype.val_injective
  have dimension : Module.finrank ℝ B.toLinearMap.range = Module.finrank ℝ U :=
    LinearMap.finrank_range_of_inj injective
  obtain ⟨R, boundR, factorization⟩ := BoundedImageSection.exists_section B Q
    dimension imageNonnegative imageTransverse
  have sectionBound : R.toLinearMap.normDet ≤
      GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) M := by
    apply RectangularJacobianBounds.normDet_le (stdOrthonormalBasis ℝ U) R imageNonnegative
    intro i
    calc
      ‖R ((stdOrthonormalBasis ℝ U) i)‖ ≤ ‖R‖ * ‖(stdOrthonormalBasis ℝ U) i‖ := R.le_opNorm _
      _ = ‖R‖ := by rw [OrthonormalBasis.norm_eq_one, mul_one]
      _ ≤ M := boundR
  exact TransverseGraphJacobianComparison.tangent_le U D J A Q R annihilates
    factorization small interaction leafSlope sectionBound
end LeanShared.EndpointJacobianComparison
