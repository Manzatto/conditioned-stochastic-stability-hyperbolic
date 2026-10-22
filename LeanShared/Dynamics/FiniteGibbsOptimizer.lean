module

public import LeanShared.Dynamics.FiniteGibbsVariational
public import LeanShared.Dynamics.FiniteRelativeEntropy

/-! The normalized Gibbs weights are constructed explicitly and proved to
be the unique optimizer of the actual finite entropy-plus-energy functional. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.FiniteGibbsOptimizer
variable {I : Type*} [Fintype I] [Nonempty I]

@[expose] def partition (a : I → ℝ) : ℝ := ∑ i, Real.exp (a i)
@[expose] def weights (a : I → ℝ) (i : I) : ℝ := Real.exp (a i)/partition a
@[expose] def value (p a : I → ℝ) : ℝ := -(∑ i, p i*Real.log (p i))+(∑ i, p i*a i)

theorem partition_positive (a : I → ℝ) : 0 < partition a :=
  Finset.sum_pos (fun i _ => Real.exp_pos (a i)) Finset.univ_nonempty

theorem weights_positive (a : I → ℝ) (i : I) : 0 < weights a i :=
  div_pos (Real.exp_pos _) (partition_positive a)

theorem weights_total (a : I → ℝ) : ∑ i, weights a i=1 := by
  simp only [weights,div_eq_mul_inv,←Finset.sum_mul]
  exact mul_inv_cancel₀ (partition_positive a).ne'

private theorem score_formula (p a : I → ℝ) (total : ∑ i, p i=1) :
    (∑ i, p i*Real.log (weights a i/p i))=value p a-Real.log (partition a) := by
  have term (i : I) : p i*Real.log (weights a i/p i) =
      p i*a i-p i*Real.log (partition a)-p i*Real.log (p i) := by
    by_cases zero : p i=0
    · simp only [zero,zero_mul,sub_self]
    rw [Real.log_div (weights_positive a i).ne' zero]
    have logarithm : Real.log (weights a i)=a i-Real.log (partition a) := by
      rw [weights,Real.log_div (Real.exp_ne_zero _) (partition_positive a).ne',Real.log_exp]
    rw [logarithm]
    ring
  simp_rw [term]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,total,one_mul]
  dsimp only [value]
  ring

/-- Exact equality identifies the explicit normalized Gibbs weights. -/
theorem equality_iff (p a : I → ℝ) (nonnegative : ∀ i, 0 ≤ p i) (total : ∑ i, p i=1) :
    value p a=Real.log (partition a) ↔ p=weights a := by
  have eq := FiniteRelativeEntropy.score_eq_zero_iff p (weights a) nonnegative
    (weights_positive a) total (weights_total a)
  rw [score_formula p a total,sub_eq_zero] at eq
  exact eq

theorem value_weights (a : I → ℝ) : value (weights a) a=Real.log (partition a) :=
  (equality_iff (weights a) a (fun i => (weights_positive a i).le) (weights_total a)).mpr rfl

/-- The optimizer, its normalization and its uniqueness are actual proofs;
no finite Gibbs or variational source is assumed. -/
theorem unique_optimizer (a : I → ℝ) :
    (∀ i, 0 < weights a i) ∧ (∑ i, weights a i=1) ∧
    ∀ p : I → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i=1) →
      value p a ≤ value (weights a) a ∧ (value p a=value (weights a) a ↔ p=weights a) := by
  refine ⟨weights_positive a,weights_total a,fun p nonnegative total => ?_⟩
  rw [value_weights]
  exact ⟨FiniteGibbsVariational.entropy_energy_le_log_partition p a nonnegative total,
    equality_iff p a nonnegative total⟩

end LeanShared.FiniteGibbsOptimizer
