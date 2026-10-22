module

public import LeanShared.Dynamics.OneSidedAbelEigenfunction

/-! Every literal predecessor contributes a positive term to the actual
transfer sum.  Zeros of a nonnegative eigenfunction therefore propagate
backwards through every actual finite prehistory.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

omit [DiscreteTopology A] [CompactSpace A] in
theorem weightedTransfer_branch_lower (ψ : C(FuturePath R, ℝ)) (f : FuturePath R → ℝ)
    (nonnegative : ∀ a, 0 ≤ f a) (b : FuturePath R) :
    Real.exp (ψ b) * f b ≤ weightedTransfer ψ f (futureShift b) := by
  classical
  let j := initialSymbol b
  have edge : R j.val ((futureShift b).val 0) := futurePath_edge b 0
  have member : futureShift b ∈ {a : FuturePath R | R j.val (a.val 0)} := edge
  have branch : prependOrStay j (futureShift b) = b := by
    rw [prependOrStay, dite_eq_left edge]
    exact futurePrepend_shift b
  have term : {a : FuturePath R | R j.val (a.val 0)}.indicator
      (fun a => Real.exp (ψ (prependOrStay j a)) * f (prependOrStay j a)) (futureShift b) =
      Real.exp (ψ b) * f b := by rw [Set.indicator_of_mem member, branch]
  rw [← term]
  dsimp only [weightedTransfer]
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun k : AdmittedSymbol R => {a : FuturePath R | R k.val (a.val 0)}.indicator
      (fun a => Real.exp (ψ (prependOrStay k a)) * f (prependOrStay k a)) (futureShift b))
    (fun k _ => Set.indicator_nonneg (fun a _ => mul_nonneg (Real.exp_pos _).le (nonnegative _)) _)
    (Finset.mem_univ j)

theorem eigenfunction_zero_predecessor (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (nonnegative : ∀ a, 0 ≤ h a) (eigen : weightedTransferOperator ψ h = eigenvalue • h)
    (b : FuturePath R) (zero : h (futureShift b) = 0) : h b = 0 := by
  have branch := weightedTransfer_branch_lower ψ h nonnegative b
  have identity := congrArg (fun f : C(FuturePath R, ℝ) => f (futureShift b)) eigen
  change weightedTransfer ψ h (futureShift b) = eigenvalue * h (futureShift b) at identity
  rw [zero, mul_zero] at identity
  rw [identity] at branch
  have nonpositive : h b ≤ 0 := by nlinarith [Real.exp_pos (ψ b)]
  exact le_antisymm nonpositive (nonnegative b)

theorem eigenfunction_zero_prehistory (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (nonnegative : ∀ a, 0 ≤ h a) (eigen : weightedTransferOperator ψ h = eigenvalue • h)
    (n : ℕ) (b : FuturePath R) (zero : h ((futureShift : FuturePath R → FuturePath R)^[n] b) = 0) : h b = 0 := by
  induction n generalizing b with
  | zero => exact zero
  | succ n induction =>
    rw [iterate_succ_apply] at zero
    exact eigenfunction_zero_predecessor ψ h eigenvalue nonnegative eigen b (induction (futureShift b) zero)

end LeanShared.BilateralShadowingCoding
