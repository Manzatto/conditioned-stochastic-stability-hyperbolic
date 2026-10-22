module
public import LeanShared.Analysis.RectangularJacobianBounds

/-! A genuine inverse derivative norm controls the reciprocal rectangular
Jacobian on EVERY tangent plane. This is the coarse, word-dependent
constant allowed in the weak remainder, not the principal coefficient. -/
public noncomputable section
namespace LeanShared.RestrictedInverseJacobianBound
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem bound (A:E≃L[ℝ] E) (W:Submodule ℝ E) {K:ℝ} (nonnegative:0≤K)
    (inverse:‖A.symm.toContinuousLinearMap‖≤K):
    1≤GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ W)) K*
      (A.toLinearMap.domRestrict W).normDet:=by
  let B:W→L[ℝ] E:=A.toContinuousLinearMap.comp W.subtypeL
  have injective:Function.Injective B:=A.injective.comp Subtype.val_injective
  let V:=B.toLinearMap.range
  have dimension:Module.finrank ℝ V=Module.finrank ℝ W:=LinearMap.finrank_range_of_inj injective
  let b:OrthonormalBasis (Fin (Module.finrank ℝ W)) ℝ V:=
    (stdOrthonormalBasis ℝ V).reindex (finCongr dimension)
  let R:V→L[ℝ] E:=A.symm.toContinuousLinearMap.comp V.subtypeL
  have rbound:R.toLinearMap.normDet≤GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ W)) K:=by
    apply RectangularJacobianBounds.normDet_le b R nonnegative
    intro i
    calc
      ‖R (b i)‖≤‖A.symm.toContinuousLinearMap‖*‖(b i:E)‖:=A.symm.toContinuousLinearMap.le_opNorm _
      _≤K*‖(b i:E)‖:=mul_le_mul_of_nonneg_right inverse (norm_nonneg _)
      _=K:=by change K*‖b i‖=K;rw [b.norm_eq_one,mul_one]
  have composition:(A.symm.toLinearMap.comp B.toLinearMap)=W.subtype:=by
    apply LinearMap.ext
    intro v
    exact A.symm_apply_apply v.val
  have chain:=LinearMap.normDet_comp B.toLinearMap A.symm.toLinearMap
  rw [composition,LinearMap.normDet_subtype] at chain
  change 1=R.toLinearMap.normDet*B.toLinearMap.normDet at chain
  have estimate:=mul_le_mul_of_nonneg_right rbound (LinearMap.normDet_nonneg B.toLinearMap)
  rw [←chain] at estimate
  exact estimate
end LeanShared.RestrictedInverseJacobianBound
