module

public import ConditionedStochasticStabilityHyperbolic.Spectral.RegularCoreApproximation
import Mathlib.Tactic.Linarith

/-! A concrete two-step anisotropic tower exists for every real r>1.
The common regular exponent also exceeds all three negative orders, so the
same full regular test space can serve the distribution comparison. No
integer rounding or stronger smoothness threshold is introduced. -/

@[expose] public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.AdmissibleExponents
open RegularCoreApproximation

def loss (r : ℝ) : ℝ := (r - 1) / 16
def t (r : ℝ) (stage : Fin 3) : ℝ := (4 - (stage.val : ℝ)) * loss r
def s (r : ℝ) (stage : Fin 3) : ℝ := -(4 + (stage.val : ℝ)) * loss r
def regular (r : ℝ) : ℝ := 8 * loss r

theorem loss_positive {r : ℝ} (hr : 1 < r) : 0 < loss r := by
  dsimp [loss]
  linarith

theorem margins {r : ℝ} (hr : 1 < r) (stage : Fin 3) :
    RegularityMargins r (t r stage) (s r stage) (regular r) := by
  have hη := loss_positive hr
  have hwidth : 16 * loss r = r - 1 := by dsimp [loss]; ring
  have hk0 : 0 ≤ (stage.val : ℝ) := Nat.cast_nonneg _
  have hk2 : (stage.val : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ stage.isLt
  have hlower := mul_nonneg hk0 hη.le
  have hupper := mul_le_mul_of_nonneg_right hk2 hη.le
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp [t, s, regular] <;> nlinarith

theorem negative_order_lt_regular {r : ℝ} (hr : 1 < r) (stage : Fin 3) :
    -(s r stage) < regular r := by
  have hη := loss_positive hr
  have hk2 : (stage.val : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ stage.isLt
  have hupper := mul_le_mul_of_nonneg_right hk2 hη.le
  dsimp [s, regular]
  nlinarith

theorem successive_t (r : ℝ) (i j : Fin 3) (h : j.val = i.val + 1) :
    t r j = t r i - loss r := by
  dsimp [t]
  rw [h, Nat.cast_add, Nat.cast_one]
  ring

theorem successive_s (r : ℝ) (i j : Fin 3) (h : j.val = i.val + 1) :
    s r j = s r i - loss r := by
  dsimp [s]
  rw [h, Nat.cast_add, Nat.cast_one]
  ring

end ConditionedStochasticStabilityHyperbolic.Paper.AdmissibleExponents
