module
public import LeanShared.Analysis.OrthogonalSlopeFromDecomposition
public import Mathlib.Analysis.Normed.Operator.Prod

/-! One fixed coordinate equivalence produces fixed model planes and a
common aperture converting product cones to actual orthogonal model slopes. -/
public noncomputable section
namespace LeanShared.SplitCoordinateOrthogonalSlopes
open Set
variable {X Y H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

@[expose] def stablePlane (e : (X×Y)≃L[ℝ]H) : Submodule ℝ H :=
  (Submodule.prod (⊥ : Submodule ℝ X) ⊤).map e.toLinearMap

@[expose] def unstablePlane (e : (X×Y)≃L[ℝ]H) : Submodule ℝ H :=
  (Submodule.prod (⊤ : Submodule ℝ X) ⊥).map e.toLinearMap

theorem exists_aperture (e : (X×Y)≃L[ℝ]H) :
    ∃κ : ℝ, 0<κ ∧ κ≤1 ∧
      (∀z : X×Y,‖z.1‖≤κ*‖z.2‖ →
        ‖(stablePlane e)ᗮ.orthogonalProjectionOnto (e z)‖≤(1/8:ℝ)*‖(stablePlane e).orthogonalProjectionOnto (e z)‖) ∧
      (∀z : X×Y,‖z.2‖≤κ*‖z.1‖ →
        ‖(unstablePlane e)ᗮ.orthogonalProjectionOnto (e z)‖≤(1/8:ℝ)*‖(unstablePlane e).orthogonalProjectionOnto (e z)‖) := by
  let A := ‖e.toContinuousLinearMap‖
  let B := ‖e.symm.toContinuousLinearMap‖
  have nonnegativeA : 0≤A := norm_nonneg _
  have nonnegativeB : 0≤B := norm_nonneg _
  let κ := 1/(16*(1+A*B))
  have positiveκ : 0<κ := by dsimp only [κ]; positivity
  have capκ : κ≤1 := by
    dsimp only [κ]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<16*(1+A*B))).mpr
    nlinarith
  have small : A*B*κ≤(1/16:ℝ) := by
    dsimp only [κ]
    rw [←mul_div_assoc,mul_one]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<16*(1+A*B))).mpr
    nlinarith
  refine ⟨κ,positiveκ,capκ,?_,?_⟩
  · intro z cone
    have inverseBound := e.symm.toContinuousLinearMap.le_opNorm (e (0,z.2))
    change ‖e.symm (e (0,z.2))‖≤B*‖e (0,z.2)‖ at inverseBound
    rw [e.symm_apply_apply,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] at inverseBound
    have forwardBound := e.toContinuousLinearMap.le_opNorm (z.1,0)
    change ‖e (z.1,0)‖≤A*‖(z.1,(0:Y))‖ at forwardBound
    rw [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] at forwardBound
    have error : ‖e (z.1,0)‖≤(1/16:ℝ)*‖e (0,z.2)‖ := calc
      _ ≤ A*‖z.1‖ := forwardBound
      _ ≤ A*(κ*‖z.2‖) := mul_le_mul_of_nonneg_left cone nonnegativeA
      _ ≤ A*(κ*(B*‖e (0,z.2)‖)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left inverseBound positiveκ.le) nonnegativeA
      _ = (A*B*κ)*‖e (0,z.2)‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small (norm_nonneg _)
    have result := OrthogonalSlopeFromDecomposition.one_eighth (stablePlane e) (e (z.1,0)) (e (0,z.2))
      (Submodule.mem_map.mpr ⟨(0,z.2),by simp,rfl⟩) error
    have sum : e (z.1,0)+e (0,z.2)=e z := by
      rw [←map_add]
      exact congrArg e (Prod.ext (add_zero _) (zero_add _))
    rwa [sum] at result
  · intro z cone
    have inverseBound := e.symm.toContinuousLinearMap.le_opNorm (e (z.1,0))
    change ‖e.symm (e (z.1,0))‖≤B*‖e (z.1,0)‖ at inverseBound
    rw [e.symm_apply_apply,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] at inverseBound
    have forwardBound := e.toContinuousLinearMap.le_opNorm (0,z.2)
    change ‖e ((0:X),z.2)‖≤A*‖((0:X),z.2)‖ at forwardBound
    rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] at forwardBound
    have error : ‖e (0,z.2)‖≤(1/16:ℝ)*‖e (z.1,0)‖ := calc
      _ ≤ A*‖z.2‖ := forwardBound
      _ ≤ A*(κ*‖z.1‖) := mul_le_mul_of_nonneg_left cone nonnegativeA
      _ ≤ A*(κ*(B*‖e (z.1,0)‖)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left inverseBound positiveκ.le) nonnegativeA
      _ = (A*B*κ)*‖e (z.1,0)‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small (norm_nonneg _)
    have result := OrthogonalSlopeFromDecomposition.one_eighth (unstablePlane e) (e (0,z.2)) (e (z.1,0))
      (Submodule.mem_map.mpr ⟨(z.1,0),by simp,rfl⟩) error
    have sum : e (0,z.2)+e (z.1,0)=e z := by
      rw [←map_add]
      exact congrArg e (Prod.ext (zero_add _) (add_zero _))
    rwa [sum] at result
end LeanShared.SplitCoordinateOrthogonalSlopes
