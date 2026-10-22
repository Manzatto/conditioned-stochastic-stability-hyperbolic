module

public import LeanShared.Analysis.PositiveContinuousOperatorNorm
public import LeanShared.Dynamics.OneSidedTransferLowerBound

/-! Sharp literal uniform-operator growth for the constructed weighted
transfer: the norm of each operator power is exactly the norm of its
actual iterate of one, with a positive exponential lower bound.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function PositiveContinuousOperatorNorm
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

theorem weightedTransferOperator_positive (ψ : C(FuturePath R, ℝ)) :
    Positive (weightedTransferOperator ψ) :=
  fun f nonnegative a => weightedTransfer_nonnegative ψ f nonnegative a

theorem weightedTransferOperator_power_one (ψ : C(FuturePath R, ℝ)) (m : ℕ) :
    ((weightedTransferOperator ψ) ^ m) 1 = weightedIterateOne ψ m := by
  induction m with
  | zero => apply ContinuousMap.ext; intro a; rfl
  | succ m induction =>
    rw [pow_succ']
    change weightedTransferOperator ψ (((weightedTransferOperator ψ) ^ m) 1) = weightedIterateOne ψ (m + 1)
    rw [induction]
    apply ContinuousMap.ext
    intro a
    change weightedTransfer ψ ((weightedTransfer ψ)^[m] (fun _ => 1)) a =
      ((weightedTransfer ψ)^[m + 1] (fun _ => 1)) a
    rw [iterate_succ_apply']

theorem weightedTransferOperator_power_norm [Nonempty (FuturePath R)]
    (ψ : C(FuturePath R, ℝ)) (m : ℕ) :
    ‖(weightedTransferOperator ψ) ^ m‖ = ‖weightedIterateOne ψ m‖ := by
  rw [power_norm_eq_image_one _ (weightedTransferOperator_positive ψ), weightedTransferOperator_power_one]

theorem weightedTransferOperator_power_norm_lower [Nonempty (FuturePath R)]
    (ψ : C(FuturePath R, ℝ)) (m : ℕ) :
    (Real.exp (-‖ψ‖)) ^ m ≤ ‖(weightedTransferOperator ψ) ^ m‖ := by
  obtain ⟨a⟩ := ‹Nonempty (FuturePath R)›
  rw [weightedTransferOperator_power_norm]
  exact (weightedTransfer_iterate_one_lower ψ m a).trans (ContinuousMap.apply_le_norm _ a)

end LeanShared.BilateralShadowingCoding
