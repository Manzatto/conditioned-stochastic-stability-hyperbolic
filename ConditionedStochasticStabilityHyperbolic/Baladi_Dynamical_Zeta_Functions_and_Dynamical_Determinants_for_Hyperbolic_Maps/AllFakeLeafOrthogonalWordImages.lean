module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafNonlinearImage
public import LeanShared.Analysis.OrthogonalHalfConeGlobalWordFakeLeaves
public import LeanShared.Analysis.GlobalWordNarrowProjectionBounds
public import LeanShared.Geometry.OrthogonalProductAxisPlanes
public import LeanShared.Analysis.ProjectionConeFakeLeafSlope
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! Actual global C1 words map every member of the literal half-cone
family to an actual member: both embeddedness and the full secant condition. -/
public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared OrthogonalProductCoordinates OrthogonalRateGlobalWordFakeLeaves
variable {G X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

theorem half_cone_data (U : Submodule ℝ E) (positive : 0<Module.finrank ℝ Uᗮ) :
    ConeData U (ProjectionConeTransversality.cone U.starProjection (1/2)) := by
  let P := U.starProjection
  refine ⟨?_,?_,?_,positive,?_⟩
  · exact isClosed_le P.continuous.norm ((continuous_id.sub P.continuous).norm.const_mul (1/2:ℝ))
  · intro r hr v member
    change ‖P (r • v)‖≤(1/2:ℝ)*‖r • v-P (r • v)‖
    rw [map_smul,←smul_sub,norm_smul,norm_smul]
    have condition : ‖P v‖≤(1/2:ℝ)*‖v-P v‖ := member
    exact (mul_le_mul_of_nonneg_left condition (norm_nonneg r)).trans_eq (by ring)
  · intro v member inside
    have fixed : P v=v := U.starProjection_eq_self_iff.mpr inside
    have condition : ‖P v‖≤(1/2:ℝ)*‖v-P v‖ := member
    have bound : ‖v‖≤0 := by simpa only [fixed,sub_self,norm_zero,mul_zero] using condition
    exact norm_eq_zero.mp (le_antisymm bound (norm_nonneg _))
  · refine ⟨Uᗮ,?_,rfl⟩
    intro v member
    have zero : P v=0 := Submodule.eq_starProjection_of_mem_orthogonal U.zero_mem (by simpa using member)
    change ‖P v‖≤(1/2:ℝ)*‖v-P v‖
    rw [zero,norm_zero]
    positivity

theorem actual_half_word_image_index
    (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E)
    (positiveDimension : 0<Module.finrank ℝ Y) {a K : ℝ}
    (positive : 0<a) (contracting : a<1) (nonnegativeK : 0≤K)
    (U : G→X≃L[ℝ]X) (S : G→Y≃L[ℝ]Y)
    (stable : ∀ g, ‖(S g).toContinuousLinearMap‖≤a)
    (unstable : ∀ g, ‖(U g).symm.toContinuousLinearMap‖≤a)
    (inverseBound : ∀ g, ‖(diagonal dimension (U g) (S g)).symm.toContinuousLinearMap‖≤K)
    (H : G→E≃ₜE) (smooth : ∀ g, ContDiff ℝ 1 (H g)) (inverseSmooth : ∀ g, ContDiff ℝ 1 (H g).symm)
    (close : ∀ g x, ‖fderiv ℝ (H g) x-(diagonal dimension (U g) (S g)).toContinuousLinearMap‖≤
      OrthogonalDiagonalRatePerturbation.radius a K)
    {N : ℕ} (word : Fin N→G) (k : ℕ)
    (Γ : Index (firstPlane dimension) (ProjectionConeTransversality.cone (firstPlane dimension).starProjection (1/2))) :
    ∃ image : Index (firstPlane dimension) (ProjectionConeTransversality.cone (firstPlane dimension).starProjection (1/2)),
      image.val=prefixHomeomorph H word k '' Γ.val := by
  let V := firstPlane dimension
  let W := prefixHomeomorph H word k
  have stableDimension : Module.finrank ℝ Vᗮ=Module.finrank ℝ Y := by
    rw [←secondPlane_eq_orthogonal,secondPlane_dimension]
  have fake := OrthogonalHalfConeGlobalWordFakeLeaves.whole_word_image_zero
    dimension positiveDimension a K positive contracting nonnegativeK U S stable unstable inverseBound H
    (fun g => (smooth g).differentiable one_ne_zero) close
    (Γ := Γ.val) (by simpa only [firstPlane_projection,←stableDimension] using Γ.property.2) word k
  have actualFake : FakeLeafGeometry.leafError
      (ProjectionConeTransversality.cone V.starProjection (1/2)) (Module.finrank ℝ Vᗮ) (W '' Γ.val)=0 := by
    simpa only [V,W,firstPlane_projection,stableDimension] using fake
  have embedded : C1Embedded V (W '' Γ.val) := by
    by_cases nonempty : Nonempty Γ.val
    · let := nonempty
      exact Γ.property.1.image_local_diffeomorphism (by norm_num : (0:ℝ)≤3/2)
        (ProjectionConeFakeLeafSlope.half_cone_secants V (by rwa [stableDimension]) Γ.val Γ.property.2)
        W.toOpenPartialHomeomorph (subset_univ _)
        (GlobalWordNarrowProjectionBounds.prefix_contDiff H smooth word k).contDiffOn
        (GlobalWordNarrowProjectionBounds.prefix_inverse_contDiff H inverseSmooth word k).contDiffOn
    · have empty : Γ.val=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact nonempty ⟨⟨x,hx⟩⟩
      simpa only [empty,image_empty] using embedded_empty V
  exact ⟨⟨W '' Γ.val,embedded,actualFake⟩,rfl⟩

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
