module
public import LeanShared.Analysis.RectangularJacobianBounds

/-! Coordinate/native unstable Jacobians differ by endpoint costs only.
The comparison is for the actual encoded source plane and contains no
norm of the full derivative word. -/
public noncomputable section
namespace LeanShared.NativeCoordinateJacobianComparison
variable {F G E : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ G] [FiniteDimensional ℝ E] in
theorem postcompose_bound (A : F →L[ℝ] G) (injective : Function.Injective A)
    (B : G →L[ℝ] E) (C : ℝ) (nonnegative : 0≤C)
    (bound : ∀ v,‖B v‖≤C*‖v‖) :
    (B.comp A).toLinearMap.normDet ≤
      GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ F)) C*A.toLinearMap.normDet := by
  have dimension : Module.finrank ℝ A.toLinearMap.range=Module.finrank ℝ F :=
    LinearMap.finrank_range_of_inj injective
  let basis := (stdOrthonormalBasis ℝ A.toLinearMap.range).reindex (finCongr dimension)
  let restricted := B.comp A.toLinearMap.range.subtypeL
  have cost : restricted.toLinearMap.normDet≤
      GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ F)) C := by
    apply RectangularJacobianBounds.normDet_le basis restricted nonnegative
    intro i
    simpa only [restricted,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,
      Submodule.norm_coe,basis.norm_eq_one,mul_one] using bound ((basis i : A.toLinearMap.range):G)
  have chain := LinearMap.normDet_comp A.toLinearMap B.toLinearMap
  change (B.comp A).toLinearMap.normDet=restricted.toLinearMap.normDet*A.toLinearMap.normDet at chain
  rw [chain]
  exact mul_le_mul_of_nonneg_right cost (LinearMap.normDet_nonneg _)

omit [FiniteDimensional ℝ G] [FiniteDimensional ℝ E] in
theorem native_le_coordinate (A : F ≃L[ℝ] G) (source : F ≃L[ℝ] E) (target : G ≃L[ℝ] E)
    (U : Submodule ℝ F) (coordinate : E →L[ℝ] E)
    (intertwines : ∀ v,target (A v)=coordinate (source v))
    (Csource CtargetInverse : ℝ) (sourceNonnegative : 0≤Csource)
    (targetNonnegative : 0≤CtargetInverse)
    (sourceBound : ∀ v,‖source v‖≤Csource*‖v‖)
    (targetBound : ∀ v,‖target.symm v‖≤CtargetInverse*‖v‖) :
    (A.toLinearMap.domRestrict U).normDet ≤
      (GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ U)) CtargetInverse*
        GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ U)) Csource)*
      (coordinate.toLinearMap.domRestrict
        (source.toContinuousLinearMap.comp U.subtypeL).toLinearMap.range).normDet := by
  let S := source.toContinuousLinearMap.comp U.subtypeL
  let native := A.toContinuousLinearMap.comp U.subtypeL
  let represented := target.toContinuousLinearMap.comp native
  have injective : Function.Injective represented :=
    target.injective.comp (A.injective.comp Subtype.val_injective)
  have recovered : target.symm.toContinuousLinearMap.comp represented=native := by
    apply ContinuousLinearMap.ext
    intro v
    exact target.symm_apply_apply (A v.val)
  have post := postcompose_bound represented injective target.symm.toContinuousLinearMap
    CtargetInverse targetNonnegative targetBound
  rw [recovered] at post
  have represented_eq : represented=coordinate.comp S := by
    apply ContinuousLinearMap.ext
    intro v
    exact intertwines v.val
  have sourceCost : S.toLinearMap.normDet≤
      GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ U)) Csource := by
    apply RectangularJacobianBounds.normDet_le (stdOrthonormalBasis ℝ U) S sourceNonnegative
    intro i
    rw [show S ((stdOrthonormalBasis ℝ U) i)=
      source (((stdOrthonormalBasis ℝ U) i : U):F) from rfl]
    simpa only [Submodule.norm_coe,OrthonormalBasis.norm_eq_one,mul_one] using
      sourceBound (((stdOrthonormalBasis ℝ U) i : U):F)
  have chain := LinearMap.normDet_comp S.toLinearMap coordinate.toLinearMap
  change (coordinate.comp S).toLinearMap.normDet=
    (coordinate.toLinearMap.domRestrict S.toLinearMap.range).normDet*S.toLinearMap.normDet at chain
  rw [represented_eq,chain] at post
  have dc : 0≤GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ U)) CtargetInverse :=
    GraphJacobian.densityBound_nonneg _
  exact post.trans ((mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left sourceCost (LinearMap.normDet_nonneg _)) dc).trans_eq (by ring))

end LeanShared.NativeCoordinateJacobianComparison
