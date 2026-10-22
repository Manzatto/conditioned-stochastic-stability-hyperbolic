module
public import LeanShared.Geometry.BoundedHolderCore

/-! Genuine interpolation between a uniform norm and a higher Hölder
increment bound, expressed in the actual bounded Hölder graph norm. -/
public noncomputable section
open Set
open scoped Topology BoundedContinuousFunction
namespace LeanShared.HolderInterpolation
variable {X : Type*} [MetricSpace X]

/-- Split pairs at an arbitrary positive length. No lower Hölder estimate
or interpolation operator is supplied as an assumption. -/
theorem increment_bound (f : X →ᵇ ℂ) {a b C δ : ℝ}
    (hb : 0 ≤ b) (hab : b < a) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ a) (x y : X) :
    ‖f x - f y‖ ≤
      max (C * δ ^ (a - b)) (2 * ‖f‖ / δ ^ b) * dist x y ^ b := by
  have ha : 0 < a := hb.trans_lt hab
  have split : a = (a - b) + b := by ring
  by_cases small : dist x y ≤ δ
  · calc
      _ ≤ C * dist x y ^ a := hf x y
      _ = (C * dist x y ^ (a - b)) * dist x y ^ b := by
        nth_rw 1 [split]
        rw [Real.rpow_add' dist_nonneg (by linarith)]
        ring
      _ ≤ (C * δ ^ (a - b)) * dist x y ^ b :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg small (sub_nonneg.mpr hab.le)) hC)
          (Real.rpow_nonneg dist_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg dist_nonneg _)
  · have hd : δ ≤ dist x y := (lt_of_not_ge small).le
    have positive : 0 < δ ^ b := Real.rpow_pos_of_pos hδ _
    calc
      _ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2 * ‖f‖ := by linarith [f.norm_coe_le_norm x, f.norm_coe_le_norm y]
      _ = (2 * ‖f‖ / δ ^ b) * δ ^ b := (div_mul_cancel₀ _ positive.ne').symm
      _ ≤ (2 * ‖f‖ / δ ^ b) * dist x y ^ b :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hd hb)
          (div_nonneg (by positivity) positive.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg dist_nonneg _)

/-- The norm on the constructed graph is bounded by the ACTUAL uniform
norm and the genuine increment constant. -/
theorem graph_norm_le (b : ℝ) (v : BoundedHolderSpace.graph X b) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x y, ‖BoundedHolderSpace.physical X b v x -
      BoundedHolderSpace.physical X b v y‖ ≤ C * dist x y ^ b) :
    ‖v‖ ≤ max ‖BoundedHolderSpace.physical X b v‖ C := by
  change max ‖v.val.1‖ ‖v.val.2‖ ≤ max ‖v.val.1‖ C
  apply max_le_max le_rfl
  apply (BoundedContinuousFunction.norm_le hC).mpr
  intro p
  have eq : v.val.2 p = BoundedHolderSpace.quotient X b
      (BoundedHolderSpace.physical X b v) p := by
    apply (mul_left_injective₀ (BoundedHolderSpace.weight_ne_zero X b p))
    change v.val.2 p * BoundedHolderSpace.weight X b p =
      BoundedHolderSpace.quotient X b (BoundedHolderSpace.physical X b v) p *
        BoundedHolderSpace.weight X b p
    rw [v.property p]
    exact (div_mul_cancel₀ _ (BoundedHolderSpace.weight_ne_zero X b p)).symm
  rw [eq]
  exact BoundedHolderSpace.quotient_bound X b (BoundedHolderSpace.physical X b v) C h p
end LeanShared.HolderInterpolation
