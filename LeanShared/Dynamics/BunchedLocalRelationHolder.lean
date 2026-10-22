module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

/-! A bounded local cocycle recurrence gives a global Hölder estimate on
an arbitrary finite-atlas pair state space. No metric or globally coherent
chart choice is needed: the next state is chosen jointly for each pair,
and the recurrence is required only below an actual validity radius. -/
public noncomputable section
open Filter
open scoped Topology
namespace LeanShared.BunchedLocalRelationHolder

theorem bound {I : Type*} (distance energy : I → ℝ)
    (q C L α M r : ℝ) (qnonnegative : 0 ≤ q) (qsmall : q < 1)
    (Lnonnegative : 0 ≤ L) (αnonnegative : 0 ≤ α)
    (Mnonnegative : 0 ≤ M) (positiveR : 0 < r) (bunched : q * L ^ α < 1)
    (distanceNonnegative : ∀ i, 0 ≤ distance i) (bounded : ∀ i, energy i ≤ M)
    (step : ∀ i, distance i < r → ∃ j : I,
      distance j ≤ L * distance i ∧
      energy i ≤ q * energy j + C * distance i ^ α) :
    ∃ H ≥ 0, ∀ i, energy i ≤ H * distance i ^ α := by
  let H := max (M / r ^ α) (C / (1 - q * L ^ α))
  have denominator : 0 < 1 - q * L ^ α := sub_pos.mpr bunched
  have powerR : 0 < r ^ α := Real.rpow_pos_of_pos positiveR α
  have Hnonnegative : 0 ≤ H :=
    (div_nonneg Mnonnegative powerR.le).trans (le_max_left _ _)
  have outerCoefficient : M ≤ H * r ^ α :=
    (div_le_iff₀ powerR).mp (le_max_left _ _)
  have innerCoefficient : C ≤ H * (1 - q * L ^ α) :=
    (div_le_iff₀ denominator).mp (le_max_right _ _)
  have outer (i : I) (large : r ≤ distance i) : energy i - H * distance i ^ α ≤ 0 := by
    have powers := Real.rpow_le_rpow positiveR.le large αnonnegative
    have weighted := mul_le_mul_of_nonneg_left powers Hnonnegative
    linarith [bounded i]
  have estimate (k : ℕ) : ∀ i, energy i - H * distance i ^ α ≤ q ^ k * M := by
    induction k with
    | zero =>
      intro i
      simp only [pow_zero, one_mul]
      exact (sub_le_self _ (mul_nonneg Hnonnegative (Real.rpow_nonneg (distanceNonnegative i) _))).trans (bounded i)
    | succ k ih =>
      intro i
      by_cases large : r ≤ distance i
      · exact (outer i large).trans (mul_nonneg (pow_nonneg qnonnegative _) Mnonnegative)
      · obtain ⟨j, expansion, recurrence⟩ := step i (lt_of_not_ge large)
        have powers : distance j ^ α ≤ L ^ α * distance i ^ α := by
          calc
            _ ≤ (L * distance i) ^ α := Real.rpow_le_rpow (distanceNonnegative j) expansion αnonnegative
            _ = _ := Real.mul_rpow Lnonnegative (distanceNonnegative i)
        have scaled := mul_le_mul_of_nonneg_right innerCoefficient
          (Real.rpow_nonneg (distanceNonnegative i) α)
        have weighted := mul_le_mul_of_nonneg_left powers (mul_nonneg qnonnegative Hnonnegative)
        have barrier : energy i - H * distance i ^ α ≤ q * (energy j - H * distance j ^ α) := by
          nlinarith
        calc
          _ ≤ q * (energy j - H * distance j ^ α) := barrier
          _ ≤ q * (q ^ k * M) := mul_le_mul_of_nonneg_left (ih j) qnonnegative
          _ = q ^ (k + 1) * M := by rw [pow_succ]; ring
  have limit : Tendsto (fun k : ℕ => q ^ k * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one qnonnegative qsmall).mul_const M
  refine ⟨H, Hnonnegative, fun i => ?_⟩
  exact sub_nonpos.mp (ge_of_tendsto limit (Eventually.of_forall (fun k => estimate k i)))

end LeanShared.BunchedLocalRelationHolder
