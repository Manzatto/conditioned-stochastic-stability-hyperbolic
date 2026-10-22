module
public import LeanShared.Analysis.AlmostProjectionRetraction
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

public noncomputable section
namespace LeanShared.FiniteHilbertSpectralRetraction
open Set
open scoped Matrix.Norms.L2Operator
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

@[expose] def coordinates : (E →L[ℝ] E) ≃⋆ₐ[ℝ]
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (stdOrthonormalBasis ℝ E).repr.conjStarAlgEquiv.trans
    (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm

@[expose] def retract (P : E →L[ℝ] E) : E →L[ℝ] E :=
  coordinates.symm (AlmostProjectionRetraction.retract (coordinates P))

theorem norm_conjugate_le (a : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) :
    ‖a.conjStarAlgEquiv P‖≤‖P‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.norm_map] using P.le_opNorm (a.symm x)

theorem norm_conjugate (a : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) :
    ‖a.conjStarAlgEquiv P‖=‖P‖ := by
  apply le_antisymm (norm_conjugate_le a P)
  have reverse := norm_conjugate_le a.symm (a.conjStarAlgEquiv P)
  rw [← a.symm_conjStarAlgEquiv,StarAlgEquiv.symm_apply_apply] at reverse
  exact reverse

theorem norm_coordinates (P : E →L[ℝ] E) : ‖coordinates P‖=‖P‖ := by
  rw [Matrix.cstar_norm_def]
  simpa only [coordinates,StarAlgEquiv.trans_apply,StarAlgEquiv.apply_symm_apply]
    using norm_conjugate (stdOrthonormalBasis ℝ E).repr P

private theorem self_coordinates (P : E →L[ℝ] E) (self : IsSelfAdjoint P) :
    IsSelfAdjoint (coordinates P) := by
  change star (coordinates P)=coordinates P
  rw [← map_star coordinates,self.star_eq]

 theorem fixes (P : E →L[ℝ] E) (self : IsSelfAdjoint P) (idem : IsIdempotentElem P) :
    retract P=P := by
  have hi : IsIdempotentElem (coordinates P) := by
    change coordinates P * coordinates P=coordinates P
    rw [← map_mul,idem.eq]
  unfold retract
  rw [AlmostProjectionRetraction.fixes _ (self_coordinates P self) hi]
  exact coordinates.symm_apply_apply P

theorem selfAdjoint (P : E →L[ℝ] E) : IsSelfAdjoint (retract P) := by
  change star (coordinates.symm (AlmostProjectionRetraction.retract (coordinates P))) = _
  rw [← map_star coordinates.symm,(AlmostProjectionRetraction.selfAdjoint (coordinates P)).star_eq]
  rfl

theorem idempotent (P : E →L[ℝ] E) (self : IsSelfAdjoint P)
    (small : ‖P^2-P‖<(3/16:ℝ)) : IsIdempotentElem (retract P) := by
  have defect : ‖coordinates P ^ 2-coordinates P‖=‖P^2-P‖ := by
    rw [← map_pow,← map_sub,norm_coordinates]
  have hi := AlmostProjectionRetraction.idempotent (coordinates P)
    (self_coordinates P self) (defect.trans_lt small)
  change coordinates.symm (AlmostProjectionRetraction.retract (coordinates P)) *
    coordinates.symm (AlmostProjectionRetraction.retract (coordinates P)) = _
  rw [← map_mul,hi.eq]
  rfl

theorem continuousOn : ContinuousOn (retract : (E →L[ℝ] E) → (E →L[ℝ] E))
    {P | IsSelfAdjoint P ∧ ‖P^2-P‖<(3/16:ℝ)} := by
  have forward := (coordinates (E := E)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous
  have backward := (coordinates (E := E)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.symm.continuous
  apply backward.comp_continuousOn
  apply AlmostProjectionRetraction.continuousOn.comp forward.continuousOn
  intro P hP
  refine ⟨self_coordinates P hP.1,?_⟩
  change ‖coordinates P ^ 2-coordinates P‖<(3/16:ℝ)
  rw [← map_pow,← map_sub,norm_coordinates]
  exact hP.2

set_option backward.isDefEq.respectTransparency false in
theorem conjugate (a : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) (self : IsSelfAdjoint P) :
    retract (a.conjStarAlgEquiv P)=a.conjStarAlgEquiv (retract P) := by
  let q := (coordinates (E := E)).symm.trans
    (a.conjStarAlgEquiv.trans (coordinates (E := F)))
  have continuousq : Continuous q :=
    q.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous
  have hself : IsSelfAdjoint (q (coordinates P)) := by
    change star (q (coordinates P))=q (coordinates P)
    rw [← map_star q,(self_coordinates P self).star_eq]
  have natural := StarAlgHomClass.map_cfc (S := ℝ) q
    AlmostProjectionRetraction.cutoff (coordinates P)
    AlmostProjectionRetraction.cutoff_continuous.continuousOn continuousq
    (self_coordinates P self) hself
  apply (coordinates (E := F)).injective
  change coordinates (coordinates.symm (cfc AlmostProjectionRetraction.cutoff
    (coordinates (a.conjStarAlgEquiv P)))) =
    coordinates (a.conjStarAlgEquiv (retract P))
  rw [StarAlgEquiv.apply_symm_apply]
  simpa only [retract,AlmostProjectionRetraction.retract,
    q,StarAlgEquiv.trans_apply,StarAlgEquiv.symm_apply_apply] using natural.symm
end LeanShared.FiniteHilbertSpectralRetraction
