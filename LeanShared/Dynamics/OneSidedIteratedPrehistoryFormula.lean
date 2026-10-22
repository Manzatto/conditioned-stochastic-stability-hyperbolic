module

public import LeanShared.Dynamics.OneSidedPrehistoryTransferFormula

/-! Every actual transfer iterate is exactly the weighted finite sum
over its literal inverse-orbit fiber, with the full orbit energy.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  {R : A → A → Prop}

omit [DiscreteTopology A] in
theorem complexWeightedTransfer_iterate_prehistory (ψ : FuturePath R → ℝ) (f : FuturePath R → ℂ)
    (n : ℕ) (a : FuturePath R) :
    ((complexWeightedTransfer ψ)^[n] f) a =
      ∑ b : FuturePrehistory n a,
        (Real.exp (orbitSum futureShift ψ n b.val) : ℂ) * f b.val := by
  classical
  induction n generalizing a with
  | zero =>
    change f a = _
    rw [Finset.sum_eq_single (futurePrehistoryZero a)]
    · simp only [orbitSum, Finset.range_zero, Finset.sum_empty, Real.exp_zero,
        Complex.ofReal_one, one_mul, futurePrehistoryZero]
    · intro b _ different
      exact False.elim (different (futurePrehistory_zero_unique a b))
    · intro missing
      exact False.elim (missing (Finset.mem_univ _))
  | succ n induction =>
    rw [iterate_succ_apply']
    rw [complexWeightedTransfer_prehistory_one]
    have expansion :
        (∑ c : FuturePrehistory 1 a, (Real.exp (ψ c.val) : ℂ) * ((complexWeightedTransfer ψ)^[n] f) c.val) =
        ∑ c : FuturePrehistory 1 a, ∑ b : FuturePrehistory n c.val,
          (Real.exp (ψ c.val) : ℂ) * ((Real.exp (orbitSum futureShift ψ n b.val) : ℂ) * f b.val) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [induction c.val, Finset.mul_sum]
    rw [expansion]
    have flatten := Fintype.sum_sigma (fun d : (Σ c : FuturePrehistory 1 a, FuturePrehistory n c.val) =>
      (Real.exp (ψ d.1.val) : ℂ) * ((Real.exp (orbitSum futureShift ψ n d.2.val) : ℂ) * f d.2.val))
    rw [← flatten]
    symm
    apply Fintype.sum_equiv (futurePrehistorySuccEquiv n a)
    intro b
    change (Real.exp (orbitSum futureShift ψ (n + 1) b.val) : ℂ) * f b.val =
      (Real.exp (ψ ((futureShift : FuturePath R → FuturePath R)^[n] b.val)) : ℂ) *
        ((Real.exp (orbitSum futureShift ψ n b.val) : ℂ) * f b.val)
    have energy : orbitSum futureShift ψ (n + 1) b.val =
        orbitSum futureShift ψ n b.val + ψ ((futureShift : FuturePath R → FuturePath R)^[n] b.val) :=
      Finset.sum_range_succ _ _
    rw [energy, Real.exp_add, Complex.ofReal_mul]
    ring

variable [CompactSpace A]

theorem complexWeightedTransferOperator_power_prehistory (ψ : C(FuturePath R, ℝ)) (f : C(FuturePath R, ℂ))
    (n : ℕ) (a : FuturePath R) :
    ((complexWeightedTransferOperator ψ) ^ n) f a =
      ∑ b : FuturePrehistory n a,
        (Real.exp (orbitSum futureShift ψ n b.val) : ℂ) * f b.val := by
  have powers (m : ℕ) : (fun a => ((complexWeightedTransferOperator ψ) ^ m) f a) =
      ((complexWeightedTransfer ψ)^[m] f) := by
    induction m with
    | zero => rfl
    | succ m induction =>
      rw [pow_succ', iterate_succ_apply']
      change complexWeightedTransfer ψ (fun a => ((complexWeightedTransferOperator ψ) ^ m) f a) = _
      rw [induction]
  rw [show ((complexWeightedTransferOperator ψ) ^ n) f a = ((complexWeightedTransfer ψ)^[n] f) a from congrFun (powers n) a]
  exact complexWeightedTransfer_iterate_prehistory ψ f n a

end LeanShared.BilateralShadowingCoding
