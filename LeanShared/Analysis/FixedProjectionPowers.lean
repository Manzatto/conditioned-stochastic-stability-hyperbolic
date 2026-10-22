module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-! Removing an invariant scalar-one projection gives the exact
positive-power remainder T^n minus the projection.
-/

public section
namespace LeanShared.FixedProjectionPowers
variable {B : Type*} [Ring B]

theorem power_mul_projection (T P : B) (fixed : T * P = P) (n : ℕ) : T ^ n * P = P := by
  induction n with
  | zero => rw [pow_zero, one_mul]
  | succ n induction => rw [pow_succ', mul_assoc, induction, fixed]

theorem sub_projection_power (T P : B) (idempotent : P * P = P)
    (right : T * P = P) (left : P * T = P) (n : ℕ) :
    (T - P) ^ (n + 1) = T ^ (n + 1) - P := by
  induction n with
  | zero => rw [Nat.zero_add, pow_one, pow_one]
  | succ n induction =>
    rw [show n + 1 + 1 = (n + 1) + 1 by rfl, pow_succ, induction, sub_mul, mul_sub, mul_sub,
      power_mul_projection T P right (n + 1), left, idempotent, ← pow_succ]
    noncomm_ring

end LeanShared.FixedProjectionPowers
