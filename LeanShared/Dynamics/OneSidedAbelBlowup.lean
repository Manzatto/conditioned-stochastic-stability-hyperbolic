module

public import LeanShared.Dynamics.OneSidedSupersolutionRadius

/-! An actual quantitative Abel blowup estimate at the finite positive
coefficient radius.  It follows from the literal resolvent identity and
positive supersolution order bounds; divergence is not assumed.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
open scoped NNReal ENNReal
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

@[expose] def abelRadiusReal (ψ : C(FuturePath R, ℝ)) : ℝ := (abelRadius ψ).toReal

theorem weightedAbel_ge_one (ψ : C(FuturePath R, ℝ)) (t : ℝ≥0)
    (inside : (t : ℝ≥0∞) < abelRadius ψ) (a : FuturePath R) : 1 ≤ weightedAbel ψ t a := by
  have summable := weightedAbel_summable_of_lt_radius ψ t inside
  have identity := congrArg (fun f : C(FuturePath R, ℝ) => f a) (weightedAbel_resolvent_identity ψ t summable)
  change weightedAbel ψ t a - (t : ℝ) * weightedTransferOperator ψ (weightedAbel ψ t) a = 1 at identity
  have positive : 0 ≤ weightedTransferOperator ψ (weightedAbel ψ t) a :=
    weightedTransfer_nonnegative ψ _ (weightedAbel_nonnegative ψ t t.property summable) a
  have product : 0 ≤ (t : ℝ) * weightedTransferOperator ψ (weightedAbel ψ t) a := mul_nonneg t.property positive
  calc
    1 = weightedAbel ψ t a - (t : ℝ) * weightedTransferOperator ψ (weightedAbel ψ t) a := identity.symm
    _ ≤ weightedAbel ψ t a := sub_le_self _ product

variable [Nonempty (FuturePath R)]

theorem abelRadiusReal_positive (ψ : C(FuturePath R, ℝ)) : 0 < abelRadiusReal ψ :=
  ENNReal.toReal_pos (abelRadius_positive ψ).ne' (abelRadius_lt_top ψ).ne

theorem coe_lt_abelRadiusReal (ψ : C(FuturePath R, ℝ)) (t : ℝ≥0)
    (inside : (t : ℝ≥0∞) < abelRadius ψ) : (t : ℝ) < abelRadiusReal ψ := by
  exact (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (abelRadius_lt_top ψ).ne).mpr inside

theorem weightedAbel_norm_gt_one (ψ : C(FuturePath R, ℝ)) (t : ℝ≥0) (positiveT : 0 < t)
    (inside : (t : ℝ≥0∞) < abelRadius ψ) : 1 < ‖weightedAbel ψ t‖ := by
  obtain ⟨a⟩ := ‹Nonempty (FuturePath R)›
  have summable := weightedAbel_summable_of_lt_radius ψ t inside
  have identity := congrArg (fun f : C(FuturePath R, ℝ) => f a) (weightedAbel_resolvent_identity ψ t summable)
  change weightedAbel ψ t a - (t : ℝ) * weightedTransferOperator ψ (weightedAbel ψ t) a = 1 at identity
  have lower : Real.exp (-‖ψ‖) ≤ weightedTransferOperator ψ (weightedAbel ψ t) a := by
    change Real.exp (-‖ψ‖) ≤ weightedTransfer ψ (weightedAbel ψ t) a
    simpa only [mul_one] using weightedTransfer_lower_bound ψ (weightedAbel ψ t) 1 zero_le_one
      (weightedAbel_ge_one ψ t inside) a
  have positive : 0 < (t : ℝ) := by exact_mod_cast positiveT
  have point : 1 < weightedAbel ψ t a := by
    nlinarith [mul_pos positive (Real.exp_pos (-‖ψ‖)), mul_le_mul_of_nonneg_left lower t.property]
  exact point.trans_le (ContinuousMap.apply_le_norm _ a)

theorem weightedAbel_norm_radius_lower (ψ : C(FuturePath R, ℝ)) (t : ℝ≥0) (positiveT : 0 < t)
    (inside : (t : ℝ≥0∞) < abelRadius ψ) :
    abelRadiusReal ψ / (abelRadiusReal ψ - t) ≤ ‖weightedAbel ψ t‖ := by
  let h := weightedAbel ψ t
  let M := ‖h‖
  let q := (M - 1) / ((t : ℝ) * M)
  have positive : 0 < (t : ℝ) := by exact_mod_cast positiveT
  have large : 1 < M := weightedAbel_norm_gt_one ψ t positiveT inside
  have positiveM : 0 < M := zero_lt_one.trans large
  have positiveDenominator : 0 < (t : ℝ) * M := mul_pos positive positiveM
  have positiveQ : 0 < q := div_pos (sub_pos.mpr large) positiveDenominator
  have majorant : ∀ a, 1 ≤ h a := weightedAbel_ge_one ψ t inside
  have summable := weightedAbel_summable_of_lt_radius ψ t inside
  have supersolution (a : FuturePath R) : weightedTransferOperator ψ h a ≤ q * h a := by
    have identity := congrArg (fun f : C(FuturePath R, ℝ) => f a) (weightedAbel_resolvent_identity ψ t summable)
    change h a - (t : ℝ) * weightedTransferOperator ψ h a = 1 at identity
    have rearranged : (t : ℝ) * weightedTransferOperator ψ h a = h a - 1 := by linarith
    have bound : h a ≤ M := ContinuousMap.apply_le_norm h a
    apply (mul_le_mul_iff_right₀ positiveDenominator).mp
    calc
      _ = ((t : ℝ) * weightedTransferOperator ψ h a) * M := by ring
      _ = (h a - 1) * M := by rw [rearranged]
      _ ≤ (M - 1) * h a := by nlinarith
      _ = (q * h a) * ((t : ℝ) * M) := by
        have cancel : q * ((t : ℝ) * M) = M - 1 := div_mul_cancel₀ _ positiveDenominator.ne'
        nlinarith [cancel]
      _ = ((t : ℝ) * M) * (q * h a) := by ring
  have radius := abelRadius_lower_of_supersolution ψ h q positiveQ majorant supersolution
  have realBound : q⁻¹ ≤ abelRadiusReal ψ := by
    have bound := ENNReal.toReal_mono (abelRadius_lt_top ψ).ne radius
    simpa only [ENNReal.coe_toReal, NNReal.coe_inv, Real.coe_toNNReal q positiveQ.le, abelRadiusReal] using bound
  have ratioBound : (t : ℝ) * M / (M - 1) ≤ abelRadiusReal ψ := by
    simpa only [q, inv_div] using realBound
  have inequality := (div_le_iff₀ (sub_pos.mpr large)).mp ratioBound
  change abelRadiusReal ψ / (abelRadiusReal ψ - t) ≤ M
  apply (div_le_iff₀ (sub_pos.mpr (coe_lt_abelRadiusReal ψ t inside))).mpr
  nlinarith

end LeanShared.BilateralShadowingCoding
