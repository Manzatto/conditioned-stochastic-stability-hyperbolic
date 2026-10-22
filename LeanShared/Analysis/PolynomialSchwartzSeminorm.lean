module
public import LeanShared.Analysis.ObliqueSchwartzDecay

/-! A polynomially weighted pointwise bound controls the literal finite
Schwartz seminorm used by the fake-leaf pairing estimate. -/
public noncomputable section
open scoped SchwartzMap
namespace LeanShared.ObliqueSchwartzDecay
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem seminorm_le (f : 𝓢(E,ℂ)) (m : ℕ) {B : ℝ} (nonnegative : 0 ≤ B)
    (weighted : ∀ x, (1+‖x‖)^m*‖f x‖ ≤ B) : seminorm m f ≤ B := by
  apply Seminorm.finset_sup_apply_le nonnegative
  intro j member
  have below := Finset.mem_Iic.mp member
  have zero : j.2=0 := Nat.eq_zero_of_le_zero below.2
  apply SchwartzMap.seminorm_le_bound ℂ j.1 j.2 f nonnegative
  intro x
  rw [zero,norm_iteratedFDeriv_zero]
  have power : ‖x‖^j.1 ≤ (1+‖x‖)^m :=
    (pow_le_pow_left₀ (norm_nonneg x) (by linarith) j.1).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg x]) below.1)
  exact (mul_le_mul_of_nonneg_right power (norm_nonneg _)).trans (weighted x)
end LeanShared.ObliqueSchwartzDecay
