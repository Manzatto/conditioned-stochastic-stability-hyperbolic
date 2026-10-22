module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Pressure cancellation for two specified orbit words. The resulting
correlation constant depends only on the fixed transition gap and Gibbs
constants, and is independent of both word lengths. -/
public section
namespace LeanShared.ThermodynamicDefinitions

theorem normalized_gluing_lower (A H P D J g L M a b S T mass : ℝ)
    (positiveA : 0 < A) (positiveH : 0 < H)
    (nonnegativeA : 0 ≤ a) (nonnegativeB : 0 ≤ b)
    (first : a ≤ H * Real.exp (-L * P) * S)
    (second : b ≤ H * Real.exp (-M * P) * T)
    (packing : A * Real.exp (-(L + M + g) * P) *
      (Real.exp (-(2 * D + g * J)) * S * T) ≤ mass) :
    (A / H ^ 2 * Real.exp (-(2 * D + g * (J + P)))) * a * b ≤ mass := by
  let C := A / H ^ 2 * Real.exp (-(2 * D + g * (J + P)))
  have positive : 0 ≤ C := by dsimp [C]; positivity
  have product : C * a * b ≤
      C * (H * Real.exp (-L * P) * S) * (H * Real.exp (-M * P) * T) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left first positive
    · exact second
    · exact nonnegativeB
    · exact mul_nonneg positive (nonnegativeA.trans first)
  have exponents : Real.exp (-(2 * D + g * (J + P))) *
      Real.exp (-L * P) * Real.exp (-M * P) =
      Real.exp (-(L + M + g) * P) * Real.exp (-(2 * D + g * J)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have identity : C * (H * Real.exp (-L * P) * S) *
      (H * Real.exp (-M * P) * T) =
      A * Real.exp (-(L + M + g) * P) *
        (Real.exp (-(2 * D + g * J)) * S * T) := by
    calc
      _ = A * (Real.exp (-(2 * D + g * (J + P))) *
          Real.exp (-L * P) * Real.exp (-M * P)) * S * T := by
        dsimp [C]
        field_simp [ne_of_gt positiveH]
      _ = _ := by rw [exponents]; ring
  exact product.trans (identity.le.trans packing)

end LeanShared.ThermodynamicDefinitions
