module
public import LeanShared.Analysis.PowerGrowthResolvent
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! An actual convergent Neumann representation of the resolvent. -/
public noncomputable section
namespace LeanShared.ResolventNeumannSeries
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem hasSum (a : A) (z : ℂ) (hz : ‖a‖ < ‖z‖) :
    HasSum (fun n : ℕ => z⁻¹ • (z⁻¹ • a) ^ n) (resolvent a z) := by
  have hzpos : 0 < ‖z‖ := (norm_nonneg a).trans_lt hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  let q := z⁻¹ • a
  have hq : ‖q‖ < 1 := by
    rw [show q = z⁻¹ • a from rfl, norm_smul, norm_inv]
    exact (inv_mul_lt_one₀ hzpos).mpr hz
  have sum := hasSum_geom_series_inverse q hq
  let G := Ring.inverse (1-q)
  let B := z⁻¹ • G
  have shift : z • (1-q) = algebraMap ℂ A z-a := by
    simp only [q, smul_sub, smul_smul, mul_inv_cancel₀ hz0, one_smul,
      Algebra.algebraMap_eq_smul_one]
  have left : (algebraMap ℂ A z-a)*B=1 := by
    rw [←shift]
    dsimp only [B]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hz0, one_smul]
    exact Ring.mul_inverse_cancel _ (isUnit_one_sub_of_norm_lt_one hq)
  have right : B*(algebraMap ℂ A z-a)=1 := by
    rw [←shift]
    dsimp only [B]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hz0, one_smul]
    exact Ring.inverse_mul_cancel _ (isUnit_one_sub_of_norm_lt_one hq)
  have res := spectrum.mem_resolventSet_of_left_right_inverse left right
  have formula : resolvent a z = B :=
    left_inv_eq_right_inv (Ring.inverse_mul_cancel _ res) left
  rw [formula]
  exact sum.const_smul z⁻¹
end LeanShared.ResolventNeumannSeries
