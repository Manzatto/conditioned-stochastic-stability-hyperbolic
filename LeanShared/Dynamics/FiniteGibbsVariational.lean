module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The actual finite Gibbs variational inequality, including zero
probability atoms, proved from the scalar logarithm inequality. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.FiniteGibbsVariational
variable {I : Type*} [Fintype I] [Nonempty I]

theorem entropy_energy_le_log_partition (p a : I → ℝ)
    (nonnegative : ∀ i, 0 ≤ p i) (total : ∑ i, p i=1) :
    -(∑ i, p i*Real.log (p i))+(∑ i, p i*a i) ≤ Real.log (∑ i, Real.exp (a i)) := by
  let Z := ∑ i, Real.exp (a i)
  have hZ : 0 < Z := Finset.sum_pos (fun i _ => Real.exp_pos (a i)) Finset.univ_nonempty
  let q := fun i => Real.exp (a i)/Z
  have hq (i : I) : 0 < q i := div_pos (Real.exp_pos _) hZ
  have totalQ : ∑ i, q i=1 := by
    simp only [q,div_eq_mul_inv,←Finset.sum_mul]
    exact mul_inv_cancel₀ hZ.ne'
  have term (i : I) : p i*Real.log (q i/p i) ≤ q i-p i := by
    by_cases zero : p i=0
    · simpa only [zero,zero_mul,sub_zero] using (hq i).le
    have hp : 0 < p i := lt_of_le_of_ne (nonnegative i) (Ne.symm zero)
    have logarithm := Real.log_le_sub_one_of_pos (div_pos (hq i) hp)
    have product := mul_le_mul_of_nonneg_left logarithm hp.le
    have cancel : p i*(q i/p i-1)=q i-p i := by field_simp
    exact product.trans_eq cancel
  have summed : ∑ i, p i*Real.log (q i/p i) ≤ 0 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => term i)
    simpa only [Finset.sum_sub_distrib,totalQ,total,sub_self] using h
  have expand (i : I) : p i*Real.log (q i/p i) =
      p i*a i-p i*Real.log Z-p i*Real.log (p i) := by
    by_cases zero : p i=0
    · simp only [zero,zero_mul,sub_self]
    have hp : 0 < p i := lt_of_le_of_ne (nonnegative i) (Ne.symm zero)
    rw [Real.log_div (hq i).ne' hp.ne']
    have logq : Real.log (q i)=a i-Real.log Z := by
      dsimp only [q]
      rw [Real.log_div (Real.exp_ne_zero _) hZ.ne',Real.log_exp]
    rw [logq]
    ring
  simp_rw [expand] at summed
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,total,one_mul] at summed
  linarith

end LeanShared.FiniteGibbsVariational
