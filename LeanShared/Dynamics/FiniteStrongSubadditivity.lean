module

public import LeanShared.Dynamics.FiniteEntropyHomogeneous

/-! Strong subadditivity, proved for finite measures with null atoms.
Equivalently, further conditioning cannot increase Shannon entropy. -/
public section
open scoped BigOperators
namespace LeanShared.FiniteStrongSubadditivity
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- H(I,J,K)+H(I) ≤ H(I,J)+H(I,K), including arbitrary total mass. -/
theorem entropy_strong_subadditive (p : I → J → K → ℝ)
    (nonnegative : ∀ i j k, 0 ≤ p i j k) :
    -(∑ i, ∑ j, ∑ k, p i j k*Real.log (p i j k)) -
      (∑ i, (∑ j, ∑ k, p i j k)*Real.log (∑ j, ∑ k, p i j k)) ≤
    -(∑ i, ∑ j, (∑ k, p i j k)*Real.log (∑ k, p i j k)) -
      (∑ i, ∑ k, (∑ j, p i j k)*Real.log (∑ j, p i j k)) := by
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    FiniteEntropyHomogeneous.entropy_joint_le (p i) (nonnegative i))
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_neg_distrib] at bound
  linarith

end LeanShared.FiniteStrongSubadditivity
