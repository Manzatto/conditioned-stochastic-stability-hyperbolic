module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Constructing the actual resolvent from an all-power growth bound. The
Neumann series converges even when the one-step operator norm exceeds |z|.
This supplies the initial outer resolvent region in the KL argument. -/

public noncomputable section
open Filter
open scoped Topology Ring
namespace LeanShared.PowerGrowthResolvent
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- An all-power growth estimate constructs the inverse spectral shift and
its quantitative resolvent bound outside the growth disk. -/
theorem exists_resolvent (a : A) (C R : ℝ) (hR : 0 ≤ R)
    (growth : ∀ n : ℕ, ‖a ^ n‖ ≤ C * R ^ n)
    (z : ℂ) (hz : R < ‖z‖) :
    z ∈ resolventSet ℂ a ∧ ‖resolvent a z‖ ≤ C / (‖z‖ - R) := by
  have hzpos : 0 < ‖z‖ := hR.trans_lt hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  let q := z⁻¹ • a
  let r := R / ‖z‖
  have hr0 : 0 ≤ r := div_nonneg hR hzpos.le
  have hr1 : r < 1 := (div_lt_one hzpos).mpr hz
  have scalarSum : HasSum (fun n : ℕ => C * r ^ n) (C * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left C
  have bound (n : ℕ) : ‖q ^ n‖ ≤ C * r ^ n := by
    simp only [q, smul_pow, norm_smul, norm_pow, norm_inv]
    calc
      ‖z‖⁻¹ ^ n * ‖a ^ n‖ ≤ ‖z‖⁻¹ ^ n * (C * R ^ n) :=
        mul_le_mul_of_nonneg_left (growth n) (pow_nonneg (inv_nonneg.mpr hzpos.le) n)
      _ = C * r ^ n := by simp only [r, div_eq_mul_inv, mul_pow]; ring
  have summable : Summable (fun n : ℕ => q ^ n) := scalarSum.summable.of_norm_bounded bound
  let G := ∑' n : ℕ, q ^ n
  have normG : ‖G‖ ≤ C * (1 - r)⁻¹ := summable.hasSum.norm_le_of_bounded scalarSum bound
  have shift : z • (1 - q) = algebraMap ℂ A z - a := by
    simp only [q, smul_sub, smul_smul, mul_inv_cancel₀ hz0, one_smul, Algebra.algebraMap_eq_smul_one]
  let B := z⁻¹ • G
  have left : (algebraMap ℂ A z - a) * B = 1 := by
    rw [← shift]
    dsimp only [B]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hz0, one_smul]
    exact summable.one_sub_mul_tsum_pow
  have right : B * (algebraMap ℂ A z - a) = 1 := by
    rw [← shift]
    dsimp only [B]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hz0, one_smul]
    exact summable.tsum_pow_mul_one_sub
  have hres : z ∈ resolventSet ℂ a := spectrum.mem_resolventSet_of_left_right_inverse left right
  have formula : resolvent a z = B :=
    left_inv_eq_right_inv (Ring.inverse_mul_cancel _ hres) left
  refine ⟨hres, ?_⟩
  rw [formula]
  calc
    ‖B‖ = ‖z‖⁻¹ * ‖G‖ := by simp only [B, norm_smul, norm_inv]
    _ ≤ ‖z‖⁻¹ * (C * (1 - r)⁻¹) := mul_le_mul_of_nonneg_left normG (by positivity)
    _ = C / (‖z‖ - R) := by
      dsimp only [r]
      field_simp

end LeanShared.PowerGrowthResolvent
