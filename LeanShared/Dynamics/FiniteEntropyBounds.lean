module

public import LeanShared.Dynamics.FiniteGibbsVariational

/-! Shannon entropy of finite probability weights lies between zero and the
logarithm of the number of atoms. Zero atoms are retained. -/
public section
open scoped BigOperators
namespace LeanShared.FiniteEntropyBounds
variable {I : Type*} [Fintype I] [Nonempty I]

theorem bounds (p : I → ℝ) (nonnegative : ∀ i, 0 ≤ p i) (total : ∑ i, p i=1) :
    0 ≤ -(∑ i, p i*Real.log (p i)) ∧
      -(∑ i, p i*Real.log (p i)) ≤ Real.log (Fintype.card I) := by
  constructor
  · apply neg_nonneg.mpr
    apply Finset.sum_nonpos
    intro i _
    have upper : p i ≤ 1 := by
      rw [←total]
      exact Finset.single_le_sum (fun j _ => nonnegative j) (Finset.mem_univ i)
    exact mul_nonpos_of_nonneg_of_nonpos (nonnegative i) (Real.log_nonpos (nonnegative i) upper)
  · simpa only [mul_zero,Finset.sum_const_zero,add_zero,Real.exp_zero,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using
      FiniteGibbsVariational.entropy_energy_le_log_partition p (fun _ => 0) nonnegative total

end LeanShared.FiniteEntropyBounds
