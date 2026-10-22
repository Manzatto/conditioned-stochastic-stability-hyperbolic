module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! A bounded family whose differences satisfy a common geometric tail
bound has a uniform geometric bound at every index.  The finite initial
indices are controlled by the global norm bound.
-/

public noncomputable section
namespace LeanShared.UniformGeometricTailBound
variable {P F : Type*} [NormedAddCommGroup F]

theorem exists_bound (f : P → F) (agreement : ℕ → P → P → Prop) (M L θ : ℝ)
    (nonnegativeM : 0 ≤ M) (nonnegativeL : 0 ≤ L) (positiveθ : 0 < θ) (smallθ : θ ≤ 1)
    (bounded : ∀ p, ‖f p‖ ≤ M) (threshold : ℕ)
    (tail : ∀ n ≥ threshold, ∀ p q, agreement n p q → ‖f q - f p‖ ≤ L * θ ^ n) :
    ∃ C ≥ 0, ∀ n : ℕ, ∀ p q, agreement n p q → ‖f q - f p‖ ≤ C * θ ^ n := by
  let A := 2 * M / θ ^ threshold
  have nonnegativeA : 0 ≤ A := div_nonneg (by positivity) (pow_nonneg positiveθ.le _)
  refine ⟨L + A, add_nonneg nonnegativeL nonnegativeA, fun n p q same => ?_⟩
  by_cases large : threshold ≤ n
  · exact (tail n large p q same).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right nonnegativeA) (pow_nonneg positiveθ.le _))
  · have power : θ ^ threshold ≤ θ ^ n :=
      pow_le_pow_of_le_one positiveθ.le smallθ (by omega)
    have normBound : ‖f q - f p‖ ≤ 2 * M :=
      (norm_sub_le _ _).trans (by linarith [bounded p, bounded q])
    have cancel : A * θ ^ threshold = 2 * M := by
      dsimp only [A]
      exact div_mul_cancel₀ _ (ne_of_gt (pow_pos positiveθ _))
    calc
      _ ≤ 2 * M := normBound
      _ = A * θ ^ threshold := cancel.symm
      _ ≤ A * θ ^ n := mul_le_mul_of_nonneg_left power nonnegativeA
      _ ≤ (L + A) * θ ^ n :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left nonnegativeL) (pow_nonneg positiveθ.le _)

end LeanShared.UniformGeometricTailBound
