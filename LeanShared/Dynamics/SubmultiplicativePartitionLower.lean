module

public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.EReal.Operations
import Mathlib.Tactic.Linarith

/-! Submultiplicativity and the actual limiting upper pressure force a
uniform exponential LOWER bound. Fekete's finite-residue estimate is used;
no lower growth or Gibbs normalization estimate is a premise. -/
public noncomputable section
open Filter
open scoped Topology
namespace LeanShared.SubmultiplicativePartitionLower

/-- Fekete's estimate on one residue class: a strict upper bound for `u n / n` persists
eventually along the whole sequence. -/
private theorem subadditive_eventually_div_lt {u : ℕ → ℝ} (h : Subadditive u) {L : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hL : u n / n < L) : ∀ᶠ p in atTop, u p / p < L := by
  refine .atTop_of_arithmetic hn fun r _ => ?_
  have A : Tendsto (fun x : ℝ => (u n + u r / x) / (n + r / x)) atTop (𝓝 ((u n + 0) / (n + 0))) :=
    (tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop tendsto_id).div
      (tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop tendsto_id) <| by simpa
  have B : Tendsto (fun x => (x * u n + u r) / (x * n + r)) atTop (𝓝 (u n / n)) := by
    rw [add_zero, add_zero] at A
    refine A.congr' <| (eventually_ne_atTop 0).mono fun x hx => ?_
    simp only [add_div' _ _ _ hx, div_div_div_cancel_right₀ hx, mul_comm]
  refine ((B.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hL)).mono fun k hk => ?_
  rw [mul_comm]
  refine lt_of_le_of_lt ?_ hk
  simp only [(· ∘ ·), ← Nat.cast_add, ← Nat.cast_mul]
  gcongr
  apply h.apply_mul_add_le

theorem lower_bound (a : ℕ → ℝ) (positive : ∀ n, 0 < a n)
    (C : ℝ) (positiveC : 0 < C) (P : ℝ)
    (product : ∀ n m, a (n + m) ≤ C * a n * a m)
    (pressure : limsup (fun n : ℕ => ((Real.log (a n) / (n : ℝ) : ℝ) : EReal)) atTop = (P : EReal)) :
    ∀ n : ℕ, 0 < n → Real.exp ((n : ℝ) * P) / C ≤ a n := by
  let b := fun n => Real.log C + Real.log (a n)
  have subadditive : Subadditive b := by
    intro n m
    have logarithm := Real.log_le_log (positive (n + m)) (product n m)
    rw [Real.log_mul (ne_of_gt (mul_pos positiveC (positive n))) (ne_of_gt (positive m)),
      Real.log_mul (ne_of_gt positiveC) (ne_of_gt (positive n))] at logarithm
    dsimp only [b]
    linarith
  intro n hn
  have npositive : (0 : ℝ) < n := by exact_mod_cast hn
  have pointLog : (n : ℝ) * P ≤ b n := by
    by_contra failed
    have ratio : b n / (n : ℝ) < P :=
      (div_lt_iff₀ npositive).mpr (by nlinarith [lt_of_not_ge failed])
    let L := (b n / (n : ℝ) + P) / 2
    have between : b n / (n : ℝ) < L ∧ L < P := by dsimp [L]; constructor <;> linarith
    have upper := subadditive_eventually_div_lt subadditive (Nat.ne_of_gt hn) between.1
    let η := (P - L) / 2
    have positiveη : 0 < η := by dsimp [η]; linarith [between.2]
    have error : Tendsto (fun m : ℕ => -Real.log C / (m : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        tendsto_inv_atTop_nhds_zero_nat.const_mul (-Real.log C)
    have eventual : ∀ᶠ m : ℕ in atTop,
        ((Real.log (a m) / (m : ℝ) : ℝ) : EReal) ≤ ((L + η : ℝ) : EReal) := by
      filter_upwards [upper, error.eventually (gt_mem_nhds positiveη)] with m hm he
      apply EReal.coe_le_coe_iff.mpr
      rw [neg_div] at he
      have identity : b m / (m : ℝ) = Real.log C / (m : ℝ) + Real.log (a m) / (m : ℝ) := by
        dsimp only [b]
        ring
      linarith
    have limiting := limsup_le_limsup eventual
    rw [pressure, limsup_const] at limiting
    have realLimit := EReal.coe_le_coe_iff.mp limiting
    dsimp only [η] at realLimit
    linarith [between.2]
  have exponential := Real.exp_le_exp.mpr pointLog
  change Real.exp ((n : ℝ) * P) ≤ Real.exp (Real.log C + Real.log (a n)) at exponential
  rw [Real.exp_add, Real.exp_log positiveC, Real.exp_log (positive n)] at exponential
  exact (div_le_iff₀ positiveC).mpr (by simpa only [mul_comm] using exponential)

end LeanShared.SubmultiplicativePartitionLower
