module
public import LeanShared.Analysis.CompactTwoNormMeromorphicResolvent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! A compact-square operator has an actual two-norm profile at every
positive strong rate, using its square as the compact weak map. -/
public noncomputable section
namespace LeanShared.SquareCompactTwoNormBounds
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem bounds (Q : E →L[ℂ] E) (α : ℝ) (positive : 0 < α) :
    ∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧ ∀ n x,
      ‖(Q^n) x‖ ≤ C * α^n * ‖x‖ + R^n * ‖(Q^2) x‖ := by
  rcases subsingleton_or_nontrivial E with trivial | nontrivial
  · refine ⟨1,1,zero_le_one,zero_le_one,?_⟩
    intro n x
    rw [Subsingleton.elim x (0 : E)]
    simp

  ·
    let R := ‖Q‖+1
    let C := 1+‖Q‖/α
    have hR : 1 ≤ R := by dsimp only [R]; linarith [norm_nonneg Q]
    have hQ : ‖Q‖ ≤ R := by dsimp only [R]; linarith
    have hC : 1 ≤ C := by dsimp only [C]; linarith [div_nonneg (norm_nonneg Q) positive.le]
    have product : C*α = α+‖Q‖ := by
      dsimp only [C]
      rw [add_mul, one_mul, div_mul_cancel₀ _ positive.ne']
    refine ⟨R,C,(zero_le_one.trans hR),(zero_le_one.trans hC),?_⟩
    intro n x
    rcases n with _ | n
    · simp only [pow_zero, one_apply_eq_self, mul_one, one_mul]
      nlinarith [norm_nonneg x,norm_nonneg ((Q^2) x)]
    rcases n with _ | n
    · simp only [Nat.zero_add, pow_one, product]
      have bound := Q.le_opNorm x
      have remainder : 0 ≤ R * ‖(Q^2) x‖ := mul_nonneg (zero_le_one.trans hR) (norm_nonneg _)
      nlinarith [norm_nonneg x]
    · have estimate : ‖(Q^(n+2)) x‖ ≤ ‖Q‖^n * ‖(Q^2) x‖ := by
        rw [pow_add, mul_apply_eq_comp]
        exact ((Q^n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (norm_pow_le Q n) (norm_nonneg _))
      have powers : ‖Q‖^n ≤ R^(n+2) :=
        (pow_le_pow_left₀ (norm_nonneg Q) hQ n).trans (pow_le_pow_right₀ hR (by omega))
      have weak := estimate.trans (mul_le_mul_of_nonneg_right powers (norm_nonneg _))
      have strongNonnegative : 0 ≤ C*α^(n+2)*‖x‖ := by positivity
      exact weak.trans (le_add_of_nonneg_left strongNonnegative)

variable [CompleteSpace E]
theorem meromorphicOn (Q : E →L[ℂ] E) (compact : IsCompactOperator (Q^2 : E →L[ℂ] E))
    (α : ℝ) (positive : 0 < α) : MeromorphicOn (resolvent Q) {z : ℂ | α < ‖z‖} := by
  obtain ⟨R,C,hR,hC,estimate⟩ := bounds Q α positive
  exact CompactTwoNormMeromorphicResolvent.meromorphicOn Q (Q^2) compact α R C 1
    positive.le hR hC zero_le_one (by intro n x; simpa only [one_mul] using estimate n x)
end LeanShared.SquareCompactTwoNormBounds
