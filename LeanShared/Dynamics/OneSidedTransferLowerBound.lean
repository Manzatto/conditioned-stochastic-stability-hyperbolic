module

public import LeanShared.Dynamics.OneSidedShiftFibers
public import LeanShared.Dynamics.OneSidedRatioVariation

/-! Every admitted future has an actual predecessor.  Positivity of
the literal weighted sum therefore gives a genuine exponential lower
bound for the iterates of one and their uniform norms.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

theorem futureShift_surjective : Surjective (futureShift : FuturePath R → FuturePath R) := by
  intro a
  refine ⟨futureRestriction ((shift R).symm (futureExtension a)), ?_⟩
  rw [← futureRestriction_shift, (shift R).apply_symm_apply, futureRestriction_extension]

variable [DiscreteTopology A] [CompactSpace A] [Fintype A]

theorem weightedTransfer_lower_bound (ψ : C(FuturePath R, ℝ)) (f : FuturePath R → ℝ)
    (c : ℝ) (nonnegativeC : 0 ≤ c) (lower : ∀ a, c ≤ f a) (a : FuturePath R) :
    Real.exp (-‖ψ‖) * c ≤ weightedTransfer ψ f a := by
  classical
  obtain ⟨b, fixed⟩ := futureShift_surjective a
  let j := initialSymbol b
  have edge : R j.val (a.val 0) := by
    have identity := congrArg (fun d : FuturePath R => d.val 0) fixed
    change b.val 1 = a.val 0 at identity
    change R (b.val 0) (a.val 0)
    rw [← identity]
    exact futurePath_edge b 0
  have member : a ∈ {d : FuturePath R | R j.val (d.val 0)} := edge
  have term : Real.exp (-‖ψ‖) * c ≤
      {d : FuturePath R | R j.val (d.val 0)}.indicator
        (fun d => Real.exp (ψ (prependOrStay j d)) * f (prependOrStay j d)) a := by
    rw [Set.indicator_of_mem member]
    exact mul_le_mul (Real.exp_le_exp.mpr (ContinuousMap.neg_norm_le_apply ψ _))
      (lower _) nonnegativeC (Real.exp_pos _).le
  apply term.trans
  dsimp only [weightedTransfer]
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun k : AdmittedSymbol R => {d : FuturePath R | R k.val (d.val 0)}.indicator
      (fun d => Real.exp (ψ (prependOrStay k d)) * f (prependOrStay k d)) a)
    (fun k _ => Set.indicator_nonneg
      (fun d _ => mul_nonneg (Real.exp_pos _).le (nonnegativeC.trans (lower _))) a)
    (Finset.mem_univ j)

theorem weightedTransfer_iterate_one_lower (ψ : C(FuturePath R, ℝ)) (m : ℕ) (a : FuturePath R) :
    (Real.exp (-‖ψ‖)) ^ m ≤ weightedIterateOne ψ m a := by
  induction m generalizing a with
  | zero => rfl
  | succ m induction =>
    change (Real.exp (-‖ψ‖)) ^ (m + 1) ≤ ((weightedTransfer ψ)^[m + 1] (fun _ => 1)) a
    rw [iterate_succ_apply', pow_succ']
    exact weightedTransfer_lower_bound ψ _ ((Real.exp (-‖ψ‖)) ^ m) (by positivity) induction a

theorem weightedIterateOne_norm_positive [Nonempty (FuturePath R)]
    (ψ : C(FuturePath R, ℝ)) (m : ℕ) : 0 < ‖weightedIterateOne ψ m‖ := by
  obtain ⟨a⟩ := ‹Nonempty (FuturePath R)›
  have lower := weightedTransfer_iterate_one_lower ψ m a
  have upper : weightedIterateOne ψ m a ≤ ‖weightedIterateOne ψ m‖ :=
    ContinuousMap.apply_le_norm _ a
  exact lt_of_lt_of_le (pow_pos (Real.exp_pos _) m) (lower.trans upper)

end LeanShared.BilateralShadowingCoding
