module

public import LeanShared.Dynamics.OneSidedTransferCone
public import LeanShared.Dynamics.OneSidedVariationBanach
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Uniform logarithmic distortion gives a uniform Banach variation
bound relative to the actual uniform norm.  Applied to the literal
transfer iterates of one, the constant is independent of iterate length.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A]
  {R : A → A → Prop}

private theorem exponential_chord (K t : ℝ) (nonnegative : 0 ≤ t) (small : t ≤ 1) :
    Real.exp (K * t) - 1 ≤ (Real.exp K - 1) * t := by
  have chord := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ K)
    (sub_nonneg.mpr small) nonnegative (sub_add_cancel 1 t)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at chord
  rw [mul_comm t K] at chord
  linarith

theorem prefixRatio_variation (f : C(FuturePath R, ℝ)) (θ K : ℝ)
    (nonnegativeθ : 0 ≤ θ) (smallθ : θ ≤ 1) (nonnegativeK : 0 ≤ K)
    (positiveF : ∀ a, 0 ≤ f a) (ratio : PrefixRatioBound f θ K)
    (n : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b n) :
    |f b - f a| ≤ ((Real.exp K - 1) * ‖f‖) * θ ^ n := by
  have factorNonnegative : 0 ≤ Real.exp K - 1 := sub_nonneg.mpr (Real.one_le_exp nonnegativeK)
  have increment := exponential_chord K (θ ^ n) (pow_nonneg nonnegativeθ n)
    (pow_le_one₀ nonnegativeθ smallθ)
  have upper (x y : FuturePath R) (matching : PrefixAgreement x y n) :
      f y - f x ≤ ((Real.exp K - 1) * ‖f‖) * θ ^ n := by
    have initial : f y - f x ≤ (Real.exp (K * θ ^ n) - 1) * f x := by
      nlinarith [ratio n x y matching]
    calc
      _ ≤ (Real.exp (K * θ ^ n) - 1) * f x := initial
      _ ≤ ((Real.exp K - 1) * θ ^ n) * f x := mul_le_mul_of_nonneg_right increment (positiveF x)
      _ ≤ ((Real.exp K - 1) * θ ^ n) * ‖f‖ :=
        mul_le_mul_of_nonneg_left (ContinuousMap.apply_le_norm f x)
          (mul_nonneg factorNonnegative (pow_nonneg nonnegativeθ n))
      _ = _ := by ring
  exact abs_le.mpr ⟨by linarith [upper b a (fun k hk => (same k hk).symm)], upper a b same⟩

@[expose] def ratioVariationElement (f : C(FuturePath R, ℝ)) (θ K : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ ≤ 1) (nonnegativeK : 0 ≤ K)
    (positiveF : ∀ a, 0 ≤ f a) (ratio : PrefixRatioBound f θ K) : variationGraph R θ :=
  variationElement θ positiveθ f ((Real.exp K - 1) * ‖f‖)
    (mul_nonneg (sub_nonneg.mpr (Real.one_le_exp nonnegativeK)) (norm_nonneg f))
    (prefixRatio_variation f θ K positiveθ.le smallθ nonnegativeK positiveF ratio)

theorem ratioVariationElement_norm (f : C(FuturePath R, ℝ)) (θ K : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ ≤ 1) (nonnegativeK : 0 ≤ K)
    (positiveF : ∀ a, 0 ≤ f a) (ratio : PrefixRatioBound f θ K) :
    ‖ratioVariationElement f θ K positiveθ smallθ nonnegativeK positiveF ratio‖ ≤ Real.exp K * ‖f‖ := by
  apply (variationElement_norm_le θ positiveθ f ((Real.exp K - 1) * ‖f‖)
    (mul_nonneg (sub_nonneg.mpr (Real.one_le_exp nonnegativeK)) (norm_nonneg f))
    (prefixRatio_variation f θ K positiveθ.le smallθ nonnegativeK positiveF ratio)).trans
  apply max_le
  · exact le_mul_of_one_le_left (norm_nonneg f) (Real.one_le_exp nonnegativeK)
  · exact mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) (norm_nonneg f)

variable [Fintype A]

omit [CompactSpace A] in
theorem weightedTransfer_iterate_one_continuous (ψ : C(FuturePath R, ℝ)) (m : ℕ) :
    Continuous ((weightedTransfer ψ)^[m] (fun _ => 1)) := by
  induction m with
  | zero => exact continuous_const
  | succ m induction =>
    rw [iterate_succ_apply']
    exact weightedTransfer_continuous ψ _ ψ.continuous induction

@[expose] def weightedIterateOne (ψ : C(FuturePath R, ℝ)) (m : ℕ) : C(FuturePath R, ℝ) :=
  ⟨(weightedTransfer ψ)^[m] (fun _ => 1), weightedTransfer_iterate_one_continuous ψ m⟩

@[expose] def weightedIterateOneGraph (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (m : ℕ) : variationGraph R θ :=
  ratioVariationElement (weightedIterateOne ψ m) θ (Cψ * θ / (1 - θ)) positiveθ smallθ.le
    (div_nonneg (mul_nonneg nonnegativeψ positiveθ.le) (sub_pos.mpr smallθ).le)
    (weightedTransfer_iterate_one_nonnegative ψ m)
    (weightedTransfer_iterate_one_ratio ψ θ Cψ positiveθ.le smallθ nonnegativeψ potential m)

theorem weightedIterateOneGraph_physical (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (m : ℕ) : variationPhysical θ (weightedIterateOneGraph ψ θ Cψ positiveθ smallθ nonnegativeψ potential m) =
      weightedIterateOne ψ m := rfl

theorem weightedIterateOneGraph_norm (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (m : ℕ) : ‖weightedIterateOneGraph ψ θ Cψ positiveθ smallθ nonnegativeψ potential m‖ ≤
      Real.exp (Cψ * θ / (1 - θ)) * ‖weightedIterateOne ψ m‖ :=
  ratioVariationElement_norm (weightedIterateOne ψ m) θ (Cψ * θ / (1 - θ)) positiveθ smallθ.le
    (div_nonneg (mul_nonneg nonnegativeψ positiveθ.le) (sub_pos.mpr smallθ).le)
    (weightedTransfer_iterate_one_nonnegative ψ m)
    (weightedTransfer_iterate_one_ratio ψ θ Cψ positiveθ.le smallθ nonnegativeψ potential m)

end LeanShared.BilateralShadowingCoding
