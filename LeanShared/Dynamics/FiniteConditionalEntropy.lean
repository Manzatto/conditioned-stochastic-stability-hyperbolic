module

public import LeanShared.Dynamics.FiniteEntropyBounds
public import LeanShared.Dynamics.FiniteEntropySubadditivity
import Mathlib.Tactic.FieldSimp

/-! Positivity and sharp alphabet bound for actual finite conditional
entropy, allowing zero-probability conditioning atoms. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.FiniteConditionalEntropy
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Refining a finite law cannot decrease its Shannon entropy. -/
theorem refinement_nonnegative (p : I → J → ℝ) (nonnegative : ∀ i j, 0 ≤ p i j) :
    0 ≤ -(∑ i, ∑ j, p i j*Real.log (p i j)) +
      ∑ i, (∑ j, p i j)*Real.log (∑ j, p i j) := by
  classical
  have terms (i : I) (j : J) :
      p i j*Real.log (p i j) ≤ p i j*Real.log (∑ j, p i j) := by
    by_cases zero : p i j=0
    · simp only [zero,zero_mul,le_refl]
    have positive := lt_of_le_of_ne (nonnegative i j) (Ne.symm zero)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log positive
      (Finset.single_le_sum (fun j _ => nonnegative i j) (Finset.mem_univ j))) positive.le
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => terms i j))
  simp only [←Finset.sum_mul] at sum
  linarith

private theorem row_bound (p : J → ℝ) (nonnegative : ∀ j, 0 ≤ p j) :
    -(∑ j, p j*Real.log (p j)) + (∑ j, p j)*Real.log (∑ j, p j) ≤
      (∑ j, p j)*Real.log (Fintype.card J : ℝ) := by
  classical
  let a : ℝ := ∑ j, p j
  have ha : 0 ≤ a := Finset.sum_nonneg (fun j _ => nonnegative j)
  by_cases zero : a=0
  · have vanish (j : J) : p j=0 := by
      have := Finset.single_le_sum (fun j _ => nonnegative j) (Finset.mem_univ j)
      change p j ≤ a at this
      rw [zero] at this
      exact le_antisymm this (nonnegative j)
    simp only [vanish,zero_mul,Finset.sum_const_zero,Real.log_zero,add_zero,neg_zero,le_refl]
  have positive : 0 < a := lt_of_le_of_ne ha (Ne.symm zero)
  have total : ∑ j, p j/a=1 := by
    simp_rw [div_eq_mul_inv]
    rw [←Finset.sum_mul]
    exact mul_inv_cancel₀ zero
  have nonempty : Nonempty J := by
    by_contra absent
    let : IsEmpty J := not_nonempty_iff.mp absent
    simp only [a,Finset.univ_eq_empty,Finset.sum_empty,lt_self_iff_false] at positive
  let : Nonempty J := nonempty
  have normalized := (FiniteEntropyBounds.bounds (fun j => p j/a)
    (fun j => div_nonneg (nonnegative j) ha) total).2
  have scaled := mul_le_mul_of_nonneg_left normalized ha
  have identity (j : J) : a*((p j/a)*Real.log (p j/a)) =
      p j*Real.log (p j) - p j*Real.log a := by
    by_cases zp : p j=0
    · simp only [zp,zero_div,zero_mul,sub_self,mul_zero]
    rw [Real.log_div zp zero]
    field_simp
  rw [mul_neg,Finset.mul_sum] at scaled
  simp_rw [identity,Finset.sum_sub_distrib,←Finset.sum_mul] at scaled
  change -(∑ j, p j*Real.log (p j)) + a*Real.log a ≤ a*Real.log (Fintype.card J : ℝ)
  linarith

/-- Conditional entropy is at most the total mass times log of the
conditioned alphabet size; no strictly-positive marginal is required. -/
theorem alphabet_bound (p : I → J → ℝ) (nonnegative : ∀ i j, 0 ≤ p i j) :
    -(∑ i, ∑ j, p i j*Real.log (p i j)) +
      ∑ i, (∑ j, p i j)*Real.log (∑ j, p i j) ≤
      (∑ i, ∑ j, p i j)*Real.log (Fintype.card J : ℝ) := by
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => row_bound (p i) (nonnegative i))
  simpa only [Finset.sum_add_distrib,Finset.sum_neg_distrib,←Finset.sum_mul] using sum

end LeanShared.FiniteConditionalEntropy
