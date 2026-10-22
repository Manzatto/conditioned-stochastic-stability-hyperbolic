module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The finite relative entropy inequality and its exact equality case,
including zero atoms of the tested probability vector. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.FiniteRelativeEntropy
variable {I : Type*} [Fintype I]

private theorem term_le (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    p*Real.log (q/p) ≤ q-p := by
  by_cases zero : p=0
  · simpa only [zero,zero_mul,sub_zero] using hq.le
  have positive : 0 < p := lt_of_le_of_ne hp (Ne.symm zero)
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hq positive)) positive.le
  have identity : p*(q/p-1)=q-p := by field_simp
  exact h.trans_eq identity

private theorem term_lt (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) (different : p ≠ q) :
    p*Real.log (q/p) < q-p := by
  by_cases zero : p=0
  · simpa only [zero,zero_mul,sub_zero] using hq
  have positive : 0 < p := lt_of_le_of_ne hp (Ne.symm zero)
  have unequal : q/p ≠ 1 := by
    intro equal
    exact different ((div_eq_one_iff_eq zero).mp equal).symm
  have h := mul_lt_mul_of_pos_left
    (Real.log_lt_sub_one_of_pos (div_pos hq positive) unequal) positive
  have identity : p*(q/p-1)=q-p := by field_simp
  exact h.trans_eq identity

theorem score_nonpos (p q : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (totalP : ∑ i, p i=1) (totalQ : ∑ i, q i=1) :
    ∑ i, p i*Real.log (q i/p i) ≤ 0 := by
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => term_le (p i) (q i) (hp i) (hq i))
  simpa only [Finset.sum_sub_distrib,totalP,totalQ,sub_self] using sum

/-- Equality in the finite entropy comparison identifies the actual
probability vector; positivity is required only of the reference vector. -/
theorem score_eq_zero_iff (p q : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (totalP : ∑ i, p i=1) (totalQ : ∑ i, q i=1) :
    (∑ i, p i*Real.log (q i/p i))=0 ↔ p=q := by
  classical
  constructor
  · intro equal
    by_contra different
    have witness : ∃ i, p i ≠ q i := by
      by_contra hn
      push Not at hn
      exact different (funext hn)
    obtain ⟨i,hi⟩ := witness
    have strict := Finset.sum_lt_sum
      (fun j (_ : j ∈ Finset.univ) => term_le (p j) (q j) (hp j) (hq j))
      ⟨i,Finset.mem_univ i,term_lt (p i) (q i) (hp i) (hq i) hi⟩
    rw [equal,Finset.sum_sub_distrib,totalP,totalQ,sub_self] at strict
    exact lt_irrefl 0 strict
  · intro equal
    subst p
    simp only [div_self (hq _).ne',Real.log_one,mul_zero,Finset.sum_const_zero]

end LeanShared.FiniteRelativeEntropy
