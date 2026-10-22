module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! Exact finite Shannon entropy of independent product weights, including
zero atoms. This is algebraic entropy addition, not a supplied variational
or product-equilibrium theorem. -/
public section
open scoped BigOperators
namespace LeanShared.FiniteShannonProduct

/-- Zero atoms require no artificial strict-positivity assumption. -/
theorem mul_log_product (x y : ℝ) :
    (x*y)*Real.log (x*y)=y*(x*Real.log x)+x*(y*Real.log y) := by
  by_cases hx : x=0
  · simp only [hx,zero_mul,mul_zero,Real.log_zero,add_zero]
  by_cases hy : y=0
  · simp only [hy,mul_zero,zero_mul,Real.log_zero,zero_add]
  rw [Real.log_mul hx hy]
  ring

theorem entropy_product {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℝ) (q : J → ℝ) (totalP : ∑ i, p i=1) (totalQ : ∑ j, q j=1) :
    -(∑ i, ∑ j, (p i*q j)*Real.log (p i*q j)) =
      -(∑ i, p i*Real.log (p i)) + -(∑ j, q j*Real.log (q j)) := by
  have inner (i : I) : ∑ j, (p i*q j)*Real.log (p i*q j) =
      p i*Real.log (p i)+p i*(∑ j, q j*Real.log (q j)) := by
    simp_rw [mul_log_product]
    rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,totalQ,one_mul]
  simp_rw [inner]
  rw [Finset.sum_add_distrib,←Finset.sum_mul,totalP,one_mul,neg_add]

end LeanShared.FiniteShannonProduct
