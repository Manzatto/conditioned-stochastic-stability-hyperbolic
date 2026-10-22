module
public import LeanShared.Analysis.HigherHolderTaylorRemainder
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Tactic.Linarith

/-! Compact support upgrades the genuine higher fractional Taylor remainder
to the spatially weighted estimate needed by the leaf norm. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.HigherTaylorSupportBound
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polynomial_zero_outside (f:E→ℂ) (n:ℕ) {x:E} (outside:x∉tsupport f) (y:E) :
    HigherHolderTaylorRemainder.polynomial f n x y=0 := by
  have derivative (k:ℕ) : iteratedFDeriv ℝ k f x=0 := by
    by_contra nonzero
    exact outside (support_iteratedFDeriv_subset k nonzero)
  simp only [HigherHolderTaylorRemainder.polynomial,derivative,zero_apply,smul_zero,
    Finset.sum_const_zero,zero_add]

theorem difference_bound (f:E→ℂ) (n:ℕ) (smooth:ContDiff ℝ (n+1) f) {a C R:ℝ}
    (ha:0≤a) (hC:0≤C) (hR:0≤R)
    (support:∀z∈tsupport f,‖z‖≤R)
    (holder:∀z w,‖iteratedFDeriv ℝ (n+1) f z-iteratedFDeriv ℝ (n+1) f w‖≤C*‖z-w‖^a)
    (m:ℕ) (x y:E) :
    (1+‖x‖)^m*‖f (x-y)-HigherHolderTaylorRemainder.polynomial f n x (-y)‖≤
      |(n.factorial:ℝ)⁻¹| * C*‖y‖^(a+(n+1:ℕ))*(1+R+‖y‖)^m := by
  have estimate : ‖f (x-y)-HigherHolderTaylorRemainder.polynomial f n x (-y)‖≤
      |(n.factorial:ℝ)⁻¹| * C*‖y‖^(a+(n+1:ℕ)) := by
    simpa only [←sub_eq_add_neg,norm_neg] using
      HigherHolderTaylorRemainder.bound f n smooth ha hC (fun z w=>holder w z) x (-y)
  by_cases zero:f (x-y)-HigherHolderTaylorRemainder.polynomial f n x (-y)=0
  · rw [zero,norm_zero,mul_zero]
    positivity
  have spatial:‖x‖≤R+‖y‖ := by
    by_cases inside:x∈tsupport f
    · exact (support x inside).trans (by linarith [norm_nonneg y])
    · have poly:=polynomial_zero_outside f n inside (-y)
      have first:f (x-y)≠0:=by
        intro h
        exact zero (by rw [h,poly,sub_self])
      have bound:=support (x-y) (subset_tsupport f first)
      have triangle:=norm_add_le (x-y) y
      rw [sub_add_cancel] at triangle
      linarith
  have weight:(1+‖x‖)^m≤(1+R+‖y‖)^m :=
    pow_le_pow_left₀ (by positivity) (by linarith) m
  exact (mul_le_mul weight estimate (norm_nonneg _) (by positivity)).trans_eq (mul_comm _ _)
end LeanShared.HigherTaylorSupportBound
