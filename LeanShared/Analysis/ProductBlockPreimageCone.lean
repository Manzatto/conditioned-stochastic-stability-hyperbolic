module
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! A direct preimage-cone bound for a map close to a hyperbolic diagonal
block. It uses inverse unstable contraction but never the inverse stable
norm, hence its radius is uniform over the stable block. -/
public section
namespace LeanShared.ProductBlockPreimageCone
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem bound (U : X ≃L[ℝ] X) (S : Y →L[ℝ] Y) (B : (X × Y) →L[ℝ] (X × Y))
    {a c δ κ κ' : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (hκ' : 0 ≤ κ')
    (stable : ‖S‖ ≤ a) (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ c)
    (close : ‖B - U.toContinuousLinearMap.prodMap S‖ ≤ δ)
    (positive : 0 < 1 / c - δ - κ' * δ)
    (separation : δ + κ' * (a + δ) ≤ κ * (1 / c - δ - κ' * δ))
    (z : X × Y) (target : ‖(B z).1‖ ≤ κ' * ‖(B z).2‖) : ‖z.1‖ ≤ κ * ‖z.2‖ := by
  have productNorm : ‖z‖ ≤ ‖z.1‖ + ‖z.2‖ := by
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _))
  have error : ‖(B - U.toContinuousLinearMap.prodMap S) z‖ ≤ δ * (‖z.1‖ + ‖z.2‖) :=
    ((B - U.toContinuousLinearMap.prodMap S).le_opNorm z).trans
      ((mul_le_mul_of_nonneg_right close (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left productNorm hδ))
  have first : ‖(B z).1 - U z.1‖ ≤ δ * (‖z.1‖ + ‖z.2‖) :=
    (norm_fst_le ((B - U.toContinuousLinearMap.prodMap S) z)).trans error
  have second : ‖(B z).2 - S z.2‖ ≤ δ * (‖z.1‖ + ‖z.2‖) :=
    (norm_snd_le ((B - U.toContinuousLinearMap.prodMap S) z)).trans error
  have expanded : (1 / c) * ‖z.1‖ ≤ ‖U z.1‖ := by
    have estimate := U.symm.toContinuousLinearMap.le_opNorm (U z.1)
    change ‖U.symm (U z.1)‖ ≤ _ at estimate
    rw [U.symm_apply_apply] at estimate
    have divided : ‖z.1‖ / c ≤ ‖U z.1‖ := (div_le_iff₀ hc).mpr
      ((estimate.trans (mul_le_mul_of_nonneg_right unstable (norm_nonneg _))).trans_eq (mul_comm _ _))
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using divided
  have lower : (1 / c - δ) * ‖z.1‖ - δ * ‖z.2‖ ≤ ‖(B z).1‖ := by
    have triangle := norm_sub_norm_le (U z.1) (B z).1
    rw [norm_sub_rev] at triangle
    linarith
  have contracted : ‖S z.2‖ ≤ a * ‖z.2‖ :=
    (S.le_opNorm z.2).trans (mul_le_mul_of_nonneg_right stable (norm_nonneg _))
  have upper : ‖(B z).2‖ ≤ δ * ‖z.1‖ + (a + δ) * ‖z.2‖ := by
    have triangle := norm_add_le (S z.2) ((B z).2 - S z.2)
    rw [add_sub_cancel] at triangle
    linarith
  have relation : (1 / c - δ - κ' * δ) * ‖z.1‖ ≤
      (δ + κ' * (a + δ)) * ‖z.2‖ := by
    have estimate := target.trans (mul_le_mul_of_nonneg_left upper hκ')
    nlinarith
  have final : (1 / c - δ - κ' * δ) * ‖z.1‖ ≤
      (1 / c - δ - κ' * δ) * (κ * ‖z.2‖) := by
    calc
      _ ≤ (δ + κ' * (a + δ)) * ‖z.2‖ := relation
      _ ≤ (κ * (1 / c - δ - κ' * δ)) * ‖z.2‖ :=
        mul_le_mul_of_nonneg_right separation (norm_nonneg _)
      _ = _ := by ring
  exact le_of_mul_le_mul_left final positive
end LeanShared.ProductBlockPreimageCone
