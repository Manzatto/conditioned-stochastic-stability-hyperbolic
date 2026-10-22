module

public import LeanShared.Dynamics.FiniteRelativeEntropy
import Mathlib.Tactic.Positivity

/-! Shannon subadditivity for arbitrary finite joint probability vectors,
including zero marginal and joint atoms. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.FiniteEntropyHomogeneous
variable {I J : Type*} [Fintype I] [Fintype J]

private theorem term_le (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (support : p ≠ 0 → 0 < q) :
    p*Real.log (q/p) ≤ q-p := by
  by_cases zero : p=0
  · simpa only [zero,zero_mul,sub_zero] using hq
  have positive : 0 < p := lt_of_le_of_ne hp (Ne.symm zero)
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (support zero) positive)) positive.le
  have identity : p*(q/p-1)=q-p := by field_simp
  exact h.trans_eq identity

/-- Homogeneous Shannon subadditivity for an arbitrary finite positive
measure. Its total mass need not equal one. -/
theorem entropy_joint_le (p : I → J → ℝ) (nonnegative : ∀ i j, 0 ≤ p i j)
    :
    -(∑ i, ∑ j, p i j*Real.log (p i j)) ≤
      -(∑ i, (∑ j, p i j)*Real.log (∑ j, p i j)) -
       (∑ j, (∑ i, p i j)*Real.log (∑ i, p i j)) +
       (∑ i, ∑ j, p i j)*Real.log (∑ i, ∑ j, p i j) := by
  classical
  let a : I → ℝ := fun i => ∑ j, p i j
  let b : J → ℝ := fun j => ∑ i, p i j
  have ha : ∀ i, 0 ≤ a i := fun i => Finset.sum_nonneg (fun j _ => nonnegative i j)
  have hb : ∀ j, 0 ≤ b j := fun j => Finset.sum_nonneg (fun i _ => nonnegative i j)
  have hpa (i : I) (j : J) : p i j ≤ a i :=
    Finset.single_le_sum (fun k _ => nonnegative i k) (Finset.mem_univ j)
  have hpb (i : I) (j : J) : p i j ≤ b j :=
    Finset.single_le_sum (fun k _ => nonnegative k j) (Finset.mem_univ i)
  let M : ℝ := ∑ i, ∑ j, p i j
  have mass_nonnegative : 0 ≤ M := Finset.sum_nonneg (fun i _ => ha i)
  have hpaM (i : I) : a i ≤ M := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have positiveMass (i : I) (j : J) (different : p i j ≠ 0) : 0 < M :=
    (lt_of_le_of_ne (nonnegative i j) (Ne.symm different)).trans_le ((hpa i j).trans (hpaM i))
  have terms (i : I) (j : J) := term_le (p i j) (a i*b j/M) (nonnegative i j)
    (div_nonneg (mul_nonneg (ha i) (hb j)) mass_nonnegative) (fun different =>
      div_pos (mul_pos ((lt_of_le_of_ne (nonnegative i j) (Ne.symm different)).trans_le (hpa i j))
        ((lt_of_le_of_ne (nonnegative i j) (Ne.symm different)).trans_le (hpb i j)))
      (positiveMass i j different))
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => terms i j))
  have qtotal : ∑ i, ∑ j, a i*b j/M=M := by
    simp_rw [div_eq_mul_inv]
    simp_rw [←Finset.sum_mul]
    simp_rw [←Finset.mul_sum]
    simp_rw [←Finset.sum_mul]
    have suma : ∑ i, a i=M := rfl
    have sumb : ∑ j, b j=M := by dsimp only [b,M]; rw [Finset.sum_comm]
    rw [suma,sumb]
    by_cases zero : M=0
    · simp only [zero,zero_mul]
    · field_simp
  simp_rw [Finset.sum_sub_distrib] at bound
  rw [qtotal,sub_self] at bound
  have identity (i : I) (j : J) :
      p i j*Real.log ((a i*b j/M)/p i j) =
        p i j*Real.log (a i) + p i j*Real.log (b j) -
          p i j*Real.log M - p i j*Real.log (p i j) := by
    by_cases zero : p i j=0
    · simp only [zero,zero_mul,add_zero,sub_zero]
    have positive := lt_of_le_of_ne (nonnegative i j) (Ne.symm zero)
    rw [Real.log_div (div_pos (mul_pos (positive.trans_le (hpa i j))
      (positive.trans_le (hpb i j))) (positiveMass i j zero)).ne' zero,
      Real.log_div (mul_pos (positive.trans_le (hpa i j)) (positive.trans_le (hpb i j))).ne'
        (positiveMass i j zero).ne',
      Real.log_mul (positive.trans_le (hpa i j)).ne' (positive.trans_le (hpb i j)).ne']
    ring
  simp_rw [identity,Finset.sum_sub_distrib,Finset.sum_add_distrib] at bound
  have left : ∑ i, ∑ j, p i j*Real.log (a i) = ∑ i, a i*Real.log (a i) := by
    simp only [←Finset.sum_mul,a]
  have right : ∑ i, ∑ j, p i j*Real.log (b j) = ∑ j, b j*Real.log (b j) := by
    rw [Finset.sum_comm]
    simp only [←Finset.sum_mul,b]
  rw [left,right] at bound
  simp_rw [←Finset.sum_mul] at bound
  dsimp only [a,b,M] at bound
  linarith

end LeanShared.FiniteEntropyHomogeneous
