module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Tactic.Module

/-! First resolvent identity in an arbitrary unital algebra. -/

public section
namespace LeanShared.ResolventIdentity
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Resolvents at distinct scalar arguments satisfy the divided-difference
identity, without any commutativity assumption on the algebra. -/
theorem first (a : A) (z w : 𝕜) (hz : z ∈ resolventSet 𝕜 a)
    (hw : w ∈ resolventSet 𝕜 a) (different : w ≠ z) :
    resolvent a z * resolvent a w = (w - z)⁻¹ • (resolvent a z - resolvent a w) := by
  let s := algebraMap 𝕜 A z - a
  let t := algebraMap 𝕜 A w - a
  have hleft : resolvent a z * s = 1 := Ring.inverse_mul_cancel s hz
  have hright : t * resolvent a w = 1 := Ring.mul_inverse_cancel t hw
  have difference : t - s = (w - z) • (1 : A) := by
    dsimp [t, s]
    simp only [Algebra.algebraMap_eq_smul_one]
    module
  have identity : (w - z) • (resolvent a z * resolvent a w) =
      resolvent a z - resolvent a w := by
    calc
      (w - z) • (resolvent a z * resolvent a w) =
          resolvent a z * (t - s) * resolvent a w := by
        rw [difference, mul_smul_comm, mul_one, smul_mul_assoc]
      _ = resolvent a z - resolvent a w := by
        rw [mul_sub, sub_mul, mul_assoc, hright, mul_one, hleft, one_mul]
  rw [← identity, inv_smul_smul₀ (sub_ne_zero.mpr different)]

end LeanShared.ResolventIdentity
