module

public import LeanShared.Dynamics.FiniteRelativeEntropy

/-! A finite Gibbs reference bound and a free-energy equality imply a
uniform relative-entropy bound. The scalar logarithmic estimate is proved
for every atom, including zero atoms of the tested probability. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.FiniteRelativeEntropy
variable {I : Type*} [Fintype I]

set_option maxHeartbeats 800000 in
theorem bound_of_gibbs_and_free_energy (p q energy : I → ℝ) (A N P h E D : ℝ)
    (nonnegative : ∀ i, 0 ≤ p i) (total : ∑ i, p i = 1) (positiveA : 0 < A)
    (gibbs : ∀ i, A * Real.exp (energy i - N * P) ≤ q i)
    (entropyLower : h ≤ -(∑ i, p i * Real.log (p i)))
    (energyLower : E - D ≤ ∑ i, p i * energy i)
    (freeEnergy : h + E = N * P) :
    (∑ i, p i * Real.log (p i / q i)) ≤ D - Real.log A := by
  have positiveQ (i : I) : 0 < q i :=
    (mul_pos positiveA (Real.exp_pos _)).trans_le (gibbs i)
  have logQ (i : I) : Real.log A + energy i - N * P ≤ Real.log (q i) := by
    have bound := Real.log_le_log (mul_pos positiveA (Real.exp_pos _)) (gibbs i)
    rw [Real.log_mul positiveA.ne' (Real.exp_ne_zero _), Real.log_exp] at bound
    linarith
  have term (i : I) : p i * Real.log (p i / q i) ≤
      p i * Real.log (p i) - p i * Real.log A - p i * energy i + p i * (N * P) := by
    by_cases zero : p i = 0
    · simp only [zero, zero_mul, sub_self, add_zero, le_refl]
    have pos : 0 < p i := lt_of_le_of_ne (nonnegative i) (Ne.symm zero)
    rw [Real.log_div pos.ne' (positiveQ i).ne']
    have bound := mul_le_mul_of_nonneg_left (logQ i) (nonnegative i)
    nlinarith
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun i _ => term i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    total, one_mul] at summed
  linarith

end LeanShared.FiniteRelativeEntropy
