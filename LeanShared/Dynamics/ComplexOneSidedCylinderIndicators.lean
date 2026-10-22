module

public import LeanShared.Dynamics.ComplexOneSidedCylinderApproximation
public import LeanShared.Dynamics.ComplexOneSidedLeadingVector

/-! The actual realized-prefix cylinders give a finite continuous
partition of unity in the complex Banach space, with explicit strong
norm growth at most twice θ^(-m).  These are literal cylinder indicators.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

@[expose] def complexCylinderIndicator (m : ℕ) (w : RealizedPrefix R m) : C(FuturePath R, ℂ) := by
  classical
  exact complexCylinderFunction m (fun v => if v = w then 1 else 0)

omit [Fintype A] in
theorem complexCylinderIndicator_norm_le (m : ℕ) (w : RealizedPrefix R m) :
    ‖complexCylinderIndicator m w‖ ≤ 1 := by
  classical
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro a
  change ‖if realizedPrefix m a = w then (1 : ℂ) else 0‖ ≤ 1
  split_ifs <;> simp only [norm_one, norm_zero, le_refl, zero_le_one]

omit [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A] in
theorem realizedPrefix_eq_of_agreement (m n : ℕ) (bound : m ≤ n) (a b : FuturePath R)
    (same : PrefixAgreement a b n) : realizedPrefix m a = realizedPrefix m b := by
  apply Subtype.ext
  funext i
  exact same i.val (by omega)

omit [Fintype A] in
theorem complexCylinderIndicator_variation (θ : ℝ) (positiveθ : 0 < θ) (smallθ : θ ≤ 1)
    (m : ℕ) (w : RealizedPrefix R m) (n : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b n) :
    ‖complexCylinderIndicator m w b - complexCylinderIndicator m w a‖ ≤ (2 * θ⁻¹ ^ m) * θ ^ n := by
  classical
  by_cases above : m ≤ n
  · have identity := realizedPrefix_eq_of_agreement m n above a b same
    change ‖(if realizedPrefix m b = w then (1 : ℂ) else 0) -
      (if realizedPrefix m a = w then (1 : ℂ) else 0)‖ ≤ _
    rw [identity, sub_self, norm_zero]
    positivity
  · have bound : ‖complexCylinderIndicator m w b - complexCylinderIndicator m w a‖ ≤ 2 := by
      exact (norm_sub_le _ _).trans (by linarith
        [(ContinuousMap.norm_coe_le_norm (complexCylinderIndicator m w) b).trans (complexCylinderIndicator_norm_le m w),
          (ContinuousMap.norm_coe_le_norm (complexCylinderIndicator m w) a).trans (complexCylinderIndicator_norm_le m w)])
    have powers : θ ^ m ≤ θ ^ n := pow_le_pow_of_le_one positiveθ.le smallθ (by omega)
    have amplified := mul_le_mul_of_nonneg_left powers (pow_nonneg (inv_nonneg.mpr positiveθ.le) m)
    have cancel : θ⁻¹ ^ m * θ ^ m = 1 := by rw [← mul_pow, inv_mul_cancel₀ positiveθ.ne', one_pow]
    rw [cancel] at amplified
    exact bound.trans (by nlinarith)

@[expose] def complexCylinderIndicatorVector (θ : ℝ) (positiveθ : 0 < θ) (smallθ : θ ≤ 1)
    (m : ℕ) (w : RealizedPrefix R m) : complexVariationGraph R θ :=
  complexVariationElement θ positiveθ (complexCylinderIndicator m w) (2 * θ⁻¹ ^ m) (by positivity)
    (complexCylinderIndicator_variation θ positiveθ smallθ m w)

omit [Fintype A] in
theorem complexCylinderIndicatorVector_physical (θ : ℝ) (positiveθ : 0 < θ) (smallθ : θ ≤ 1)
    (m : ℕ) (w : RealizedPrefix R m) :
    complexVariationPhysical θ (complexCylinderIndicatorVector θ positiveθ smallθ m w) = complexCylinderIndicator m w := rfl

omit [Fintype A] in
theorem complexCylinderIndicatorVector_norm (θ : ℝ) (positiveθ : 0 < θ) (smallθ : θ ≤ 1)
    (m : ℕ) (w : RealizedPrefix R m) :
    ‖complexCylinderIndicatorVector θ positiveθ smallθ m w‖ ≤ 2 * θ⁻¹ ^ m := by
  have inverse : 1 ≤ θ⁻¹ := (one_le_inv₀ positiveθ).mpr smallθ
  have powerBound : 1 ≤ θ⁻¹ ^ m := one_le_pow₀ inverse
  apply (complexVariationElement_norm_le θ positiveθ (complexCylinderIndicator m w) (2 * θ⁻¹ ^ m)
    (by positivity) (complexCylinderIndicator_variation θ positiveθ smallθ m w)).trans
  exact max_le ((complexCylinderIndicator_norm_le m w).trans (by linarith)) le_rfl

omit [CompactSpace A] in
theorem complexCylinderIndicators_sum_one (m : ℕ) :
    ∑ w : RealizedPrefix R m, complexCylinderIndicator m w = 1 := by
  classical
  apply ContinuousMap.ext
  intro a
  rw [ContinuousMap.sum_apply]
  change (∑ w : RealizedPrefix R m, if realizedPrefix m a = w then (1 : ℂ) else 0) = 1
  rw [Finset.sum_eq_single (realizedPrefix m a)]
  · exact ite_eq_left rfl
  · intro w _ different
    exact ite_eq_right (Ne.symm different)
  · intro missing
    exact False.elim (missing (Finset.mem_univ _))

theorem complexCylinderIndicatorVectors_sum_one (θ : ℝ) (positiveθ : 0 < θ) (smallθ : θ ≤ 1)
    (m : ℕ) : ∑ w : RealizedPrefix R m, complexCylinderIndicatorVector θ positiveθ smallθ m w =
      complexConstantVariation θ positiveθ 1 := by
  apply complexVariationPhysical_injective θ positiveθ
  rw [map_sum, complexConstantVariation_physical]
  simp_rw [complexCylinderIndicatorVector_physical]
  exact complexCylinderIndicators_sum_one m

end LeanShared.BilateralShadowingCoding
