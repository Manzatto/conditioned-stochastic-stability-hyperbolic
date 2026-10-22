module

public import LeanShared.Dynamics.FiniteRelativeEntropyTesting

/-! A uniform relative-entropy bound controls the tested mass of any
finite union of atoms whose reference mass is exponentially small. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.FiniteRelativeEntropy
variable {I : Type*} [Fintype I] [Nonempty I]

set_option maxHeartbeats 1000000 in
theorem subset_mass_bound (p q : I → ℝ) (s : Finset I) (t : ℝ)
    (nonnegative : ∀ i, 0 ≤ p i) (positiveQ : ∀ i, 0 < q i)
    (totalP : ∑ i, p i = 1) (totalQ : ∑ i, q i = 1)
    (small : (∑ i ∈ s, q i) ≤ Real.exp (-t)) :
    t * (∑ i ∈ s, p i) ≤ (∑ i, p i * Real.log (p i / q i)) + Real.log 2 := by
  classical
  let f := fun i => if i ∈ s then t else 0
  have test := test_function_bound p q f nonnegative positiveQ totalP
  have energy : (∑ i, p i * f i) = t * ∑ i ∈ s, p i := by
    simp only [f, mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have term (i : I) : q i * Real.exp (f i) ≤ q i + if i ∈ s then q i * Real.exp t else 0 := by
    by_cases member : i ∈ s
    · simp only [f, ite_eq_left member]
      linarith [positiveQ i]
    · simp only [f, ite_eq_right member, Real.exp_zero, mul_one, add_zero, le_refl]
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun i _ => term i)
  simp only [Finset.sum_add_distrib, totalQ, Finset.sum_ite_mem, Finset.univ_inter,
    ← Finset.sum_mul] at bound
  have cancel : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have upper : (∑ i, q i * Real.exp (f i)) ≤ 2 := by
    have scaled := mul_le_mul_of_nonneg_right small (Real.exp_nonneg t)
    rw [cancel] at scaled
    linarith
  have positiveZ : 0 < ∑ i, q i * Real.exp (f i) :=
    Finset.sum_pos (fun i _ => mul_pos (positiveQ i) (Real.exp_pos _)) Finset.univ_nonempty
  rw [energy] at test
  exact test.trans (add_le_add le_rfl (Real.log_le_log positiveZ upper))

end LeanShared.FiniteRelativeEntropy
