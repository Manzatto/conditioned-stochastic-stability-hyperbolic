module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Basic.ENNReal.BigOperators

/-! Actual finite separated sets approximate the literal weighted
partition supremum, without supplying a maximizer as background. -/
public noncomputable section
open Set Function Filter
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

theorem exists_separated_half_sum (T : X → X) (φ : X → ℝ) (K : Set X)
    (n : ℕ) (ε : ℝ)
    (nonzero : separatedPartitionSum T φ K n ε ≠ 0)
    (finite : separatedPartitionSum T φ K n ε ≠ ⊤) :
    ∃ s : Finset X, s.Nonempty ∧ Separated T K n ε s ∧
      (separatedPartitionSum T φ K n ε).toReal/2 <
        ∑ x ∈ s, Real.exp (orbitSum T φ n x) ∧
      (∑ x ∈ s, Real.exp (orbitSum T φ n x)) ≤
        (separatedPartitionSum T φ K n ε).toReal := by
  classical
  have half := ENNReal.half_lt_self nonzero finite
  unfold separatedPartitionSum at half
  obtain ⟨s,hs⟩ := lt_iSup_iff.mp half
  obtain ⟨separated,good⟩ := lt_iSup_iff.mp hs
  have upper : (∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T φ n x))) ≤
      separatedPartitionSum T φ K n ε := by
    unfold separatedPartitionSum
    exact le_iSup_of_le s (le_iSup_of_le separated le_rfl)
  have sumfinite : (∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T φ n x))) ≠ ⊤ :=
    ne_top_of_le_ne_top finite upper
  have realSum : (∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T φ n x))).toReal =
      ∑ x ∈ s, Real.exp (orbitSum T φ n x) := by
    rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
    exact Finset.sum_congr rfl (fun x _ => ENNReal.toReal_ofReal (Real.exp_pos _).le)
  have lower := (ENNReal.toReal_lt_toReal (by finiteness) sumfinite).mpr good
  rw [ENNReal.toReal_div,ENNReal.toReal_ofNat,realSum] at lower
  have upperReal := ENNReal.toReal_mono finite upper
  rw [realSum] at upperReal
  refine ⟨s,?_,separated,lower,upperReal⟩
  by_contra empty
  rw [Finset.not_nonempty_iff_eq_empty.mp empty,Finset.sum_empty] at lower
  exact (not_lt_of_ge (by positivity)) lower

end LeanShared.ThermodynamicDefinitions
