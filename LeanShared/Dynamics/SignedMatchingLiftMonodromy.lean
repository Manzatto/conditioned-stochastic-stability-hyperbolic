module

public import LeanShared.Dynamics.BilateralPermutationCocyclePeriodicity
public import LeanShared.Dynamics.TupleMatchingMonodromy
public import LeanShared.Dynamics.SubsetMatchingPathLift

/-! A genuine periodic signed matching walk lifts to a tuple with actual
permutation monodromy.  Its product of edge signs is precisely that
permutation's sign.  This is the inverse monodromy direction.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
variable {A : Type*} {R E : A → A → Prop} {k : ℕ}

theorem matching_lift_monodromy (a : Path (SubsetMatchingEdgeTransition R E k))
    (period : ℤ) (periodic : Function.Periodic a.val period) (j : ℤ) :
    (liftMatchingPath a).val (j + period) =
      (liftMatchingPath a).val j ∘ indexTransport (matchingPathPermutation a) period := by
  have permutationPeriodic : Function.Periodic (matchingPathPermutation a) period :=
    fun n => congrArg (fun e : SubsetMatchingEdge R E k => e.val.2.2) (periodic n)
  funext i
  change subsetSymbol (a.val (j + period)).val.1
    (indexTransport (matchingPathPermutation a) (j + period) i) =
    subsetSymbol (a.val j).val.1
      (indexTransport (matchingPathPermutation a) j (indexTransport (matchingPathPermutation a) period i))
  rw [periodic j, indexTransport_periodic _ period permutationPeriodic j]
  rfl

theorem matching_path_edge_sign (a : Path (SubsetMatchingEdgeTransition R E k)) (n : ℤ) :
    matchingEdgeSign (a.val n) =
      Equiv.Perm.sign (indexTransport (matchingPathPermutation a) (n + 1)) /
        Equiv.Perm.sign (indexTransport (matchingPathPermutation a) n) := by
  have step := congrArg (fun p : Equiv.Perm (Fin k) => Equiv.Perm.sign p)
    (indexTransport_step (matchingPathPermutation a) n)
  have signs : Equiv.Perm.sign (indexTransport (matchingPathPermutation a) (n + 1)) =
      Equiv.Perm.sign (matchingPathPermutation a n) *
        Equiv.Perm.sign (indexTransport (matchingPathPermutation a) n) := by
    simpa only [Equiv.Perm.sign_trans, Equiv.Perm.sign_symm] using step
  rw [signs, mul_div_cancel_right]
  rfl

theorem matching_path_sign_product (a : Path (SubsetMatchingEdgeTransition R E k)) (n : ℕ) :
    (∏ i ∈ Finset.range n, matchingEdgeSign (a.val i)) =
      Equiv.Perm.sign (indexTransport (matchingPathPermutation a) n) := by
  calc
    _ = ∏ i ∈ Finset.range n,
        Equiv.Perm.sign (indexTransport (matchingPathPermutation a) (i + 1 : ℕ)) /
          Equiv.Perm.sign (indexTransport (matchingPathPermutation a) i) := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [Nat.cast_add, Nat.cast_one] using matching_path_edge_sign a i
    _ = Equiv.Perm.sign (indexTransport (matchingPathPermutation a) n) /
        Equiv.Perm.sign (indexTransport (matchingPathPermutation a) 0) :=
      Finset.prod_range_div (fun i : ℕ => Equiv.Perm.sign (indexTransport (matchingPathPermutation a) i)) n
    _ = _ := by rw [indexTransport_zero, Equiv.Perm.sign_refl, div_one]

end LeanShared.BilateralShadowingCoding
