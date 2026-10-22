module

public import LeanShared.Dynamics.OneSidedTransferVariation

/-! For a literal weighted transfer which fixes one, the leading
coefficient in the variation estimate is the actual prepend contraction.
The estimate uses stochastic weight sums, with no alphabet-size factor.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [CompactSpace A]
  {R : A → A → Prop}

private theorem exp_relative_difference (x y C δ : ℝ) (nonnegativeC : 0 ≤ C)
    (nonnegativeδ : 0 ≤ δ) (smallδ : δ ≤ 1) (difference : |y - x| ≤ C * δ) :
    |Real.exp y - Real.exp x| ≤ Real.exp x * (Real.exp C * C) * δ := by
  have upperX : x ≤ x + C * δ := le_add_of_nonneg_right (mul_nonneg nonnegativeC nonnegativeδ)
  have upperY : y ≤ x + C * δ := by linarith [le_abs_self (y - x)]
  have derivative : ‖Real.exp y - Real.exp x‖ ≤ Real.exp (x + C * δ) * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
      (fun t ht => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr ht)
      (convex_Iic (x + C * δ)) upperX upperY
  have expBound : Real.exp (x + C * δ) ≤ Real.exp x * Real.exp C := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_of_le_one_right nonnegativeC smallδ))
      (Real.exp_pos _).le
  change |Real.exp y - Real.exp x| ≤ Real.exp (x + C * δ) * |y - x| at derivative
  calc
    _ ≤ Real.exp (x + C * δ) * |y - x| := derivative
    _ ≤ (Real.exp x * Real.exp C) * (C * δ) :=
      mul_le_mul expBound difference (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem unitalWeightedTransfer_variation (ψ f : C(FuturePath R, ℝ)) (θ Cψ Cf : ℝ)
    (nonnegativeθ : 0 ≤ θ) (smallθ : θ ≤ 1) (nonnegativeψ : 0 ≤ Cψ)
    (variationψ : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (variationF : ∀ n a b, PrefixAgreement a b n → |f b - f a| ≤ Cf * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1)
    (n : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b n) :
    |weightedTransfer ψ f b - weightedTransfer ψ f a| ≤
      (θ * Cf + θ * (Real.exp Cψ * Cψ) * ‖f‖) * θ ^ n := by
  classical
  let weight (j : AdmittedSymbol R) (c : FuturePath R) : ℝ :=
    {d : FuturePath R | R j.val (d.val 0)}.indicator
      (fun d => Real.exp (ψ (prependOrStay j d))) c
  have mass (c : FuturePath R) : ∑ j : AdmittedSymbol R, weight j c = 1 := by
    have identity := congrArg (fun g : C(FuturePath R, ℝ) => g c) unital
    change weightedTransfer ψ (fun _ => 1) c = 1 at identity
    simpa only [weightedTransfer, mul_one] using identity
  have term (j : AdmittedSymbol R) :
      ‖{c : FuturePath R | R j.val (c.val 0)}.indicator
          (fun c => Real.exp (ψ (prependOrStay j c)) * f (prependOrStay j c)) b -
        {c : FuturePath R | R j.val (c.val 0)}.indicator
          (fun c => Real.exp (ψ (prependOrStay j c)) * f (prependOrStay j c)) a‖ ≤
      weight j b * (Cf * θ ^ (n + 1)) +
        weight j a * ((Real.exp Cψ * Cψ) * ‖f‖ * θ ^ (n + 1)) := by
    have zero := same 0 (by omega)
    by_cases edgeA : R j.val (a.val 0)
    · have edgeB : R j.val (b.val 0) := by rw [← zero]; exact edgeA
      have memberA : a ∈ {c : FuturePath R | R j.val (c.val 0)} := edgeA
      have memberB : b ∈ {c : FuturePath R | R j.val (c.val 0)} := edgeB
      dsimp only [weight]
      rw [Set.indicator_of_mem memberA, Set.indicator_of_mem memberB,
        Set.indicator_of_mem memberA, Set.indicator_of_mem memberB]
      have prefixSame := futurePrepend_prefix j a b edgeA edgeB n same
      have prependA : prependOrStay j a = futurePrepend j a edgeA := by
        simp only [prependOrStay, dite_eq_left edgeA]
      have prependB : prependOrStay j b = futurePrepend j b edgeB := by
        simp only [prependOrStay, dite_eq_left edgeB]
      rw [prependA, prependB]
      let x := futurePrepend j a edgeA
      let y := futurePrepend j b edgeB
      have observable : ‖f y - f x‖ ≤ Cf * θ ^ (n + 1) := variationF (n + 1) x y prefixSame
      have distortion : ‖Real.exp (ψ y) - Real.exp (ψ x)‖ ≤
          Real.exp (ψ x) * (Real.exp Cψ * Cψ) * θ ^ (n + 1) :=
        exp_relative_difference (ψ x) (ψ y) Cψ (θ ^ (n + 1)) nonnegativeψ
          (pow_nonneg nonnegativeθ _) (pow_le_one₀ nonnegativeθ smallθ)
          (variationψ (n + 1) x y prefixSame)
      have identity : Real.exp (ψ y) * f y - Real.exp (ψ x) * f x =
          Real.exp (ψ y) * (f y - f x) + (Real.exp (ψ y) - Real.exp (ψ x)) * f x := by ring
      change ‖Real.exp (ψ y) * f y - Real.exp (ψ x) * f x‖ ≤ _
      rw [identity]
      calc
        _ ≤ ‖Real.exp (ψ y) * (f y - f x)‖ + ‖(Real.exp (ψ y) - Real.exp (ψ x)) * f x‖ := norm_add_le _ _
        _ = Real.exp (ψ y) * ‖f y - f x‖ + ‖Real.exp (ψ y) - Real.exp (ψ x)‖ * ‖f x‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (ψ y) * (Cf * θ ^ (n + 1)) +
            (Real.exp (ψ x) * (Real.exp Cψ * Cψ) * θ ^ (n + 1)) * ‖f‖ :=
          add_le_add (mul_le_mul_of_nonneg_left observable (Real.exp_pos _).le)
            (mul_le_mul distortion (f.norm_coe_le_norm _) (norm_nonneg _) (by positivity))
        _ = _ := by ring
    · have edgeB : ¬ R j.val (b.val 0) := by rw [← zero]; exact edgeA
      have memberA : a ∉ {c : FuturePath R | R j.val (c.val 0)} := edgeA
      have memberB : b ∉ {c : FuturePath R | R j.val (c.val 0)} := edgeB
      dsimp only [weight]
      rw [Set.indicator_of_notMem memberA, Set.indicator_of_notMem memberB,
        Set.indicator_of_notMem memberA, Set.indicator_of_notMem memberB]
      simp only [sub_self, norm_zero, zero_mul, add_zero, le_refl]
  rw [← Real.norm_eq_abs]
  change ‖weightedTransfer ψ f b - weightedTransfer ψ f a‖ ≤ _
  dsimp only [weightedTransfer]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : AdmittedSymbol R, ‖{c : FuturePath R | R j.val (c.val 0)}.indicator
          (fun c => Real.exp (ψ (prependOrStay j c)) * f (prependOrStay j c)) b -
        {c : FuturePath R | R j.val (c.val 0)}.indicator
          (fun c => Real.exp (ψ (prependOrStay j c)) * f (prependOrStay j c)) a‖ := norm_sum_le _ _
    _ ≤ ∑ j : AdmittedSymbol R, (weight j b * (Cf * θ ^ (n + 1)) +
        weight j a * ((Real.exp Cψ * Cψ) * ‖f‖ * θ ^ (n + 1))) :=
      Finset.sum_le_sum (fun j _ => term j)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, mass b, mass a]
      rw [pow_succ]
      ring

end LeanShared.BilateralShadowingCoding
