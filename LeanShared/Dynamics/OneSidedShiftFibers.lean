module

public import LeanShared.Dynamics.OneSidedPredecessors

/-! Admitted predecessor symbols enumerate exactly the literal fibers
of the one-sided shift.  This identifies the finite branch sum with the
usual transfer operator over actual inverse images.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Function
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

@[expose] def shiftPreimageEquiv (a : FuturePath R) :
    {b : FuturePath R // futureShift b = a} ≃
      {j : AdmittedSymbol R // R j.val (a.val 0)} where
  toFun b := ⟨initialSymbol b.val, by
    have zero := congrArg (fun c : FuturePath R => c.val 0) b.property
    change b.val.val 1 = a.val 0 at zero
    change R (b.val.val 0) (a.val 0)
    rw [← zero]
    exact futurePath_edge b.val 0⟩
  invFun j := ⟨futurePrepend j.val a j.property, futureShift_prepend j.val a j.property⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    funext n
    cases n with
    | zero => exact futurePrepend_zero _ _ _
    | succ n =>
      rw [futurePrepend_succ]
      exact (congrArg (fun c : FuturePath R => c.val n) b.property).symm
  right_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    exact futurePrepend_zero j.val a j.property

end LeanShared.BilateralShadowingCoding
