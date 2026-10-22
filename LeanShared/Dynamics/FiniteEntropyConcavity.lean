module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen

/-! Actual finite Shannon entropy is concave under arbitrary finite
probability mixtures, including null atoms and null mixture weights. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.FiniteEntropyConcavity
variable {I J : Type*} [Fintype I] [Fintype J]

theorem mixture (w : I → ℝ) (p : I → J → ℝ)
    (weights_nonnegative : ∀ i, 0 ≤ w i) (weights_total : ∑ i, w i=1)
    (nonnegative : ∀ i j, 0 ≤ p i j) :
    ∑ i, w i * (-(∑ j, p i j*Real.log (p i j))) ≤
      -(∑ j, (∑ i, w i*p i j)*Real.log (∑ i, w i*p i j)) := by
  have point (j : J) := Real.concaveOn_negMulLog.le_map_sum
    (w := w) (p := fun i => p i j) (t := Finset.univ)
    (fun i _ => weights_nonnegative i) weights_total (fun i _ => nonnegative i j)
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun j _ => point j)
  rw [Finset.sum_comm] at bound
  simpa only [smul_eq_mul,Real.negMulLog_eq_neg,Finset.sum_neg_distrib,Finset.mul_sum,mul_neg] using bound

end LeanShared.FiniteEntropyConcavity
