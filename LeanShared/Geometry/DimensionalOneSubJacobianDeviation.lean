module

public import LeanShared.Analysis.DeterminantHolderBound
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! A dimension-uniform first-order estimate for the actual determinant
factor `normDet (I - A)`.  The constant is constructed from the smooth
determinant on finitely many canonical Euclidean spaces.  Orthonormal
conjugation then makes it uniform over all Hilbert subspaces whose rank
is bounded by the given ambient dimension.
-/

public noncomputable section
open scoped BigOperators NNReal
namespace LeanShared.DimensionalOneSubJacobianDeviation

@[expose] def euclideanConstant (k : ℕ) : ℝ≥0 :=
  Classical.choose (SmoothDeterminant.exists_lipschitz_bound
    (E := EuclideanSpace ℝ (Fin k)) 2)

theorem euclidean_bound (k : ℕ)
    (A D : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : ‖A‖ ≤ 2) (hD : ‖D‖ ≤ 2) :
    |A.det - D.det| ≤ euclideanConstant k * ‖A - D‖ :=
  Classical.choose_spec (SmoothDeterminant.exists_lipschitz_bound
    (E := EuclideanSpace ℝ (Fin k)) 2) A D hA hD

/-- A finite sum is enough; no choice depends on the varying Hilbert fiber. -/
@[expose] def bound (d : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range (d + 1), (euclideanConstant k : ℝ)

theorem positive (d : ℕ) : 0 < bound d := by
  have nonnegative : 0 ≤ ∑ k ∈ Finset.range (d + 1), (euclideanConstant k : ℝ) :=
    Finset.sum_nonneg (fun k _ => (euclideanConstant k).coe_nonneg)
  dsimp [bound]
  linarith

theorem euclideanConstant_le {d k : ℕ} (dimension : k ≤ d) :
    (euclideanConstant k : ℝ) ≤ bound d := by
  have member : k ∈ Finset.range (d + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le dimension)
  have estimate := Finset.single_le_sum
    (f := fun j => (euclideanConstant j : ℝ))
    (fun j _ => (euclideanConstant j).coe_nonneg) member
  dsimp [bound]
  linarith

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

private theorem norm_conjugate_le (e : U ≃ₗᵢ[ℝ] V) (A : U →L[ℝ] U) :
    ‖e.conjStarAlgEquiv A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.norm_map] using A.le_opNorm (e.symm x)

private theorem norm_conjugate (e : U ≃ₗᵢ[ℝ] V) (A : U →L[ℝ] U) :
    ‖e.conjStarAlgEquiv A‖ = ‖A‖ := by
  apply le_antisymm (norm_conjugate_le e A)
  have reverse := norm_conjugate_le e.symm (e.conjStarAlgEquiv A)
  rw [← e.symm_conjStarAlgEquiv, StarAlgEquiv.symm_apply_apply] at reverse
  exact reverse

private theorem det_conjugate (e : U ≃ₗᵢ[ℝ] V) (A : U →L[ℝ] U) :
    (e.conjStarAlgEquiv A).det = A.det := by
  have actual : (e.conjStarAlgEquiv A).toLinearMap =
      e.toLinearEquiv.toLinearMap.comp
        (A.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap) := by
    ext v
    rfl
  change (e.conjStarAlgEquiv A).toLinearMap.det = A.toLinearMap.det
  rw [actual]
  exact LinearMap.det_conj A.toLinearMap e.toLinearEquiv

/-- The deviation bound is uniform over every Hilbert space of rank at most `d`.
Zero-dimensional fibers are included: no nontriviality assumption is needed. -/
theorem normDet_one_sub_deviation (d : ℕ) (dimension : Module.finrank ℝ U ≤ d)
    (A : U →L[ℝ] U) (small : ‖A‖ ≤ (1 / 2 : ℝ)) :
    |(ContinuousLinearMap.id ℝ U - A).toLinearMap.normDet - 1| ≤ bound d * ‖A‖ := by
  let k := Module.finrank ℝ U
  let e := (stdOrthonormalBasis ℝ U).repr
  let B := e.conjStarAlgEquiv A
  have normB : ‖B‖ = ‖A‖ := norm_conjugate e A
  have idBound : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))‖ ≤ (2 : ℝ) :=
    ContinuousLinearMap.norm_id_le.trans (by norm_num)
  have oneSubBound : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) - B‖ ≤ (2 : ℝ) := by
    have estimate := norm_sub_le (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))) B
    have identity := ContinuousLinearMap.norm_id_le (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin k))
    rw [normB] at estimate
    linarith
  have estimate := euclidean_bound k
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) - B)
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))) oneSubBound idBound
  have idDet : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))).det = 1 :=
    LinearMap.det_id
  have conjugateId : e.conjStarAlgEquiv (ContinuousLinearMap.id ℝ U) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) := map_one e.conjStarAlgEquiv
  have sameDet := det_conjugate e (ContinuousLinearMap.id ℝ U - A)
  rw [map_sub, conjugateId] at sameDet
  rw [sameDet, idDet, sub_sub_cancel_left, norm_neg, normB] at estimate
  have absolute := abs_abs_sub_abs_le_abs_sub
    (ContinuousLinearMap.id ℝ U - A).det (1 : ℝ)
  rw [abs_one] at absolute
  rw [LinearMap.normDet_eq_abs_det]
  exact absolute.trans (estimate.trans
    (mul_le_mul_of_nonneg_right (euclideanConstant_le dimension) (norm_nonneg A)))

end LeanShared.DimensionalOneSubJacobianDeviation
