module
public import LeanShared.Analysis.RectangularJacobianBounds
public import LeanShared.Analysis.NearIdentityEquivalenceBounds
public import Mathlib.Analysis.Normed.Ring.Units

/-! Determinant comparison through an actual noninvariant stable-preimage
graph. The graph interaction is controlled independently of the ambient
map's derivative norm. -/
public noncomputable section
namespace LeanShared.GraphPreimageJacobianComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem projected_graph_factor (U : Submodule ℝ E) (D : U →L[ℝ] Uᗮ)
    (J : Uᗮ →L[ℝ] U) (A : E →L[ℝ] E) (Q : E →L[ℝ] U)
    (stable : ∀ v : Uᗮ, Q (A ((J v : E) + (v : E))) = 0) :
    Q.comp (A.comp (IntrinsicGraphJacobian.graphDifferential U D)) =
      (Q.comp (A.comp U.subtypeL)).comp (ContinuousLinearMap.id ℝ U - J.comp D) := by
  apply ContinuousLinearMap.ext
  intro u
  have cancel := stable (D u)
  simp only [map_add] at cancel
  change Q (A ((u : E) + (D u : E))) = Q (A ((u - J (D u) : U) : E))
  rw [map_add, map_add, Submodule.coe_sub, map_sub, map_sub]
  have equal : Q (A (D u : E)) = -Q (A (J (D u) : E)) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using cancel
  rw [equal, sub_eq_add_neg]

/-- A norm-small graph interaction gives a uniform determinant lower bound,
proved using the actual inverse and its Jacobian, rather than assumed. -/
theorem one_sub_det_control (U : Submodule ℝ E) (T : U →L[ℝ] U)
    {κ : ℝ} (small : κ < 1) (bound : ‖T‖ ≤ κ) :
    1 ≤ GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - κ)) *
      |(ContinuousLinearMap.id ℝ U - T).det| := by
  let unit := Units.oneSub T (bound.trans_lt small)
  let R := ContinuousLinearEquiv.unitsEquiv ℝ U unit
  have same : R.toContinuousLinearMap = ContinuousLinearMap.id ℝ U - T := by
    apply ContinuousLinearMap.ext
    intro u
    change (unit : U →L[ℝ] U) u = _
    rw [show (unit : U →L[ℝ] U) = 1 - T from Units.val_oneSub T (bound.trans_lt small)]
    rfl
  have close : ‖R.toContinuousLinearMap - ContinuousLinearMap.id ℝ U‖ ≤ κ := by
    rw [same, sub_sub_cancel_left]
    exact (norm_neg T).trans_le bound
  have inverse := NearIdentityEquivalenceBounds.inverse_norm_le R κ small close
  have inverseBound : |R.symm.toContinuousLinearMap.det| ≤
      GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - κ)) := by
    rw [← LinearMap.normDet_eq_abs_det]
    apply RectangularJacobianBounds.normDet_le (stdOrthonormalBasis ℝ U)
      R.symm.toContinuousLinearMap (le_of_lt (one_div_pos.mpr (sub_pos.mpr small)))
    intro i
    calc
      _ ≤ ‖R.symm.toContinuousLinearMap‖ * ‖(stdOrthonormalBasis ℝ U) i‖ :=
        R.symm.toContinuousLinearMap.le_opNorm _
      _ = ‖R.symm.toContinuousLinearMap‖ := by rw [OrthonormalBasis.norm_eq_one, mul_one]
      _ ≤ _ := inverse
  have identity : R.symm.toContinuousLinearMap.toLinearMap.comp R.toContinuousLinearMap.toLinearMap =
      LinearMap.id := by
    apply LinearMap.ext
    intro u
    exact R.symm_apply_apply u
  have product : |R.symm.toContinuousLinearMap.det| * |R.toContinuousLinearMap.det| = 1 := by
    rw [← abs_mul, ← LinearMap.det_comp, identity, LinearMap.det_id, abs_one]
  rw [← same]
  exact product.symm.trans_le (mul_le_mul_of_nonneg_right inverseBound (abs_nonneg _))
/-- The endpoint stable-preimage graph controls the projected unstable
Jacobian without assuming invariance of the original stable subspace. -/
theorem projected_block_le (U : Submodule ℝ E) (D : U →L[ℝ] Uᗮ)
    (J : Uᗮ →L[ℝ] U) (A : E →L[ℝ] E) (Q : E →L[ℝ] U)
    (stable : ∀ v : Uᗮ, Q (A ((J v : E) + (v : E))) = 0)
    {κ : ℝ} (small : κ < 1) (bound : ‖J.comp D‖ ≤ κ) :
    |(Q.comp (A.comp U.subtypeL)).det| ≤
      GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - κ)) *
        |(Q.comp (A.comp (IntrinsicGraphJacobian.graphDifferential U D))).det| := by
  let P := Q.comp (A.comp U.subtypeL)
  let K := Q.comp (A.comp (IntrinsicGraphJacobian.graphDifferential U D))
  let R := ContinuousLinearMap.id ℝ U - J.comp D
  have factor : |K.det| = |P.det| * |R.det| := by
    have equal : K = P.comp R := projected_graph_factor U D J A Q stable
    rw [equal]
    change |(P.toLinearMap.comp R.toLinearMap).det| = _
    rw [LinearMap.det_comp, abs_mul]
  have determinant := one_sub_det_control U (J.comp D) small bound
  calc
    _ = |P.det| * 1 := (mul_one _).symm
    _ ≤ |P.det| * (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U))
        (1 / (1 - κ)) * |R.det|) := mul_le_mul_of_nonneg_left determinant (abs_nonneg _)
    _ = _ := by rw [factor]; ring
/-- The full unstable restricted Jacobian is controlled by the genuine leaf
Jacobian. Both endpoint graphs may be noninvariant. The constant depends
only on their slopes and their transverse interaction, never on `‖A‖`. -/
theorem unstable_tangent_le (U : Submodule ℝ E) (D : U →L[ℝ] Uᗮ)
    (J : Uᗮ →L[ℝ] U) (H : U →L[ℝ] Uᗮ) (A : E ≃L[ℝ] E)
    (stable : ∀ v : Uᗮ, U.orthogonalProjectionOnto
      (A ((J v : E) + (v : E))) = 0)
    (image : A.toContinuousLinearMap.comp U.subtypeL =
      (IntrinsicGraphJacobian.graphDifferential U H).comp
        (U.orthogonalProjectionOnto.comp (A.toContinuousLinearMap.comp U.subtypeL)))
    {κ Lsource Ltarget : ℝ} (small : κ < 1) (interaction : ‖J.comp D‖ ≤ κ)
    (sourceSlope : ‖D‖ ≤ Lsource) (targetSlope : ‖H‖ ≤ Ltarget) :
    (A.toLinearMap.domRestrict U).normDet ≤
      (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) Ltarget *
        GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - κ)) *
        (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U))
            ‖U.orthogonalProjectionOnto‖ *
          GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) Lsource)) *
      (A.toLinearMap.domRestrict
        (IntrinsicGraphJacobian.graphDifferential U D).toLinearMap.range).normDet := by
  let P := U.orthogonalProjectionOnto.comp (A.toContinuousLinearMap.comp U.subtypeL)
  let K := U.orthogonalProjectionOnto.comp
    (A.toContinuousLinearMap.comp (IntrinsicGraphJacobian.graphDifferential U D))
  have chain : (A.toLinearMap.domRestrict U).normDet =
      (IntrinsicGraphJacobian.graphDifferential U H).toLinearMap.normDet * |P.det| := by
    have equal := congrArg ContinuousLinearMap.toLinearMap image
    change A.toLinearMap.domRestrict U =
      (IntrinsicGraphJacobian.graphDifferential U H).toLinearMap.comp P.toLinearMap at equal
    rw [equal, LinearMap.normDet_comp_of_finrank_eq _ _ rfl,
      LinearMap.normDet_eq_abs_det]
  have graphBound : (IntrinsicGraphJacobian.graphDifferential U H).toLinearMap.normDet ≤
      GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) Ltarget := by
    rw [IntrinsicGraphJacobian.normDet_graph U (stdOrthonormalBasis ℝ U) H]
    exact GraphJacobian.density_le _ _ targetSlope
  have projected := projected_block_le U D J A.toContinuousLinearMap
    U.orthogonalProjectionOnto stable small interaction
  have tangent := RectangularJacobianBounds.graph_projected_determinant_le
    U D A U.orthogonalProjectionOnto sourceSlope
  rw [chain]
  calc
    _ ≤ GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) Ltarget *
        (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - κ)) *
          |K.det|) := mul_le_mul graphBound projected (abs_nonneg _) (GraphJacobian.densityBound_nonneg _)
    _ ≤ GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) Ltarget *
        (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - κ)) *
          ((GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U))
              ‖U.orthogonalProjectionOnto‖ *
            GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) Lsource) *
            (A.toLinearMap.domRestrict
              (IntrinsicGraphJacobian.graphDifferential U D).toLinearMap.range).normDet)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left tangent
        (GraphJacobian.densityBound_nonneg _)) (GraphJacobian.densityBound_nonneg _)
    _ = _ := by ring
end LeanShared.GraphPreimageJacobianComparison
