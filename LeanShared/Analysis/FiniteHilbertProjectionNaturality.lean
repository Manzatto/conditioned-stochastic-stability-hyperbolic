module
public import LeanShared.Analysis.ComplementaryProjectionReconstruction
public noncomputable section
namespace LeanShared.FiniteHilbertProjectionNaturality
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem inverse (a : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) (unit : IsUnit P) :
    a.conjStarAlgEquiv (Ring.inverse P)=Ring.inverse (a.conjStarAlgEquiv P) := by
  let e := a.conjStarAlgEquiv
  have mapped : IsUnit (e P) := unit.map e.toMonoidHom
  calc
    e (Ring.inverse P) = (e (Ring.inverse P)*e P)*Ring.inverse (e P) := by
      rw [mul_assoc,Ring.mul_inverse_cancel _ mapped,mul_one]
    _ = Ring.inverse (e P) := by
      rw [← map_mul,Ring.inverse_mul_cancel _ unit,map_one,one_mul]

theorem orthogonalize (a : E ≃ₗᵢ[ℝ] F) (P : E →L[ℝ] E) (idem : IsIdempotentElem P) :
    a.conjStarAlgEquiv (ContinuousIdempotentOrthogonalization.orthogonalize P)=
      ContinuousIdempotentOrthogonalization.orthogonalize (a.conjStarAlgEquiv P) := by
  have u := IdempotentSymmetrizer.isUnit P idem
  unfold ContinuousIdempotentOrthogonalization.orthogonalize
  rw [map_mul,inverse a _ u]
  congr 2
  simp only [IdempotentSymmetrizer.symmetrizer,map_sub,map_add,map_star,map_one]

theorem reconstruct (a : E ≃ₗᵢ[ℝ] F) (R S : E →L[ℝ] E) (unit : IsUnit (R-S)) :
    a.conjStarAlgEquiv (ComplementaryProjectionReconstruction.reconstruct R S)=
      ComplementaryProjectionReconstruction.reconstruct (a.conjStarAlgEquiv R) (a.conjStarAlgEquiv S) := by
  unfold ComplementaryProjectionReconstruction.reconstruct
  rw [map_mul,inverse a _ unit,map_sub]
end LeanShared.FiniteHilbertProjectionNaturality
