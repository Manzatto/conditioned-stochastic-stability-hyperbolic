module

public import LeanShared.Dynamics.OneSidedWeightedTransfer
public import LeanShared.Dynamics.OneSidedExponentialPotential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-! The actual weighted graph transfer preserves exponential prefix
variation.  The estimate separates the contracting prepend variation
of the observable from the bounded-potential distortion term.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [CompactSpace A]
  {R : A → A → Prop}

private theorem exp_difference_bound (x y M : ℝ) (hx : x ≤ M) (hy : y ≤ M) :
    ‖Real.exp y - Real.exp x‖ ≤ Real.exp M * ‖y - x‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr ht)
    (convex_Iic M) hx hy

theorem weightedTransfer_variation_bound (ψ f : C(FuturePath R, ℝ)) (θ Cψ Cf : ℝ)
    (nonnegativeθ : 0 ≤ θ) (nonnegativeψ : 0 ≤ Cψ) (nonnegativeF : 0 ≤ Cf)
    (variationψ : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (variationF : ∀ n a b, PrefixAgreement a b n → |f b - f a| ≤ Cf * θ ^ n)
    (n : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b n) :
    |weightedTransfer ψ f b - weightedTransfer ψ f a| ≤
      ((Fintype.card (AdmittedSymbol R) : ℝ) * Real.exp ‖ψ‖ * θ * (Cf + Cψ * ‖f‖)) * θ ^ n := by
  classical
  have term (j : AdmittedSymbol R) :
      ‖{c : FuturePath R | R j.val (c.val 0)}.indicator
          (fun c => Real.exp (ψ (prependOrStay j c)) * f (prependOrStay j c)) b -
        {c : FuturePath R | R j.val (c.val 0)}.indicator
          (fun c => Real.exp (ψ (prependOrStay j c)) * f (prependOrStay j c)) a‖ ≤
      Real.exp ‖ψ‖ * (Cf + Cψ * ‖f‖) * θ ^ (n + 1) := by
    have zero := same 0 (by omega)
    by_cases edgeA : R j.val (a.val 0)
    · have edgeB : R j.val (b.val 0) := by rw [← zero]; exact edgeA
      have memberA : a ∈ {c : FuturePath R | R j.val (c.val 0)} := edgeA
      have memberB : b ∈ {c : FuturePath R | R j.val (c.val 0)} := edgeB
      rw [Set.indicator_of_mem memberA, Set.indicator_of_mem memberB]
      have prefixSame := futurePrepend_prefix j a b edgeA edgeB n same
      have prependA : prependOrStay j a = futurePrepend j a edgeA := by
        simp only [prependOrStay, dite_eq_left edgeA]
      have prependB : prependOrStay j b = futurePrepend j b edgeB := by
        simp only [prependOrStay, dite_eq_left edgeB]
      rw [prependA, prependB]
      let x := futurePrepend j a edgeA
      let y := futurePrepend j b edgeB
      have potential : ‖ψ y - ψ x‖ ≤ Cψ * θ ^ (n + 1) := variationψ (n + 1) x y prefixSame
      have observable : ‖f y - f x‖ ≤ Cf * θ ^ (n + 1) := variationF (n + 1) x y prefixSame
      have weight := exp_difference_bound (ψ x) (ψ y) ‖ψ‖
        (ContinuousMap.apply_le_norm ψ x) (ContinuousMap.apply_le_norm ψ y)
      have weightBound : ‖Real.exp (ψ y) - Real.exp (ψ x)‖ ≤ Real.exp ‖ψ‖ * (Cψ * θ ^ (n + 1)) :=
        weight.trans (mul_le_mul_of_nonneg_left potential (Real.exp_pos _).le)
      have identity : Real.exp (ψ y) * f y - Real.exp (ψ x) * f x =
          Real.exp (ψ y) * (f y - f x) + (Real.exp (ψ y) - Real.exp (ψ x)) * f x := by ring
      change ‖Real.exp (ψ y) * f y - Real.exp (ψ x) * f x‖ ≤ _
      rw [identity]
      calc
        _ ≤ ‖Real.exp (ψ y) * (f y - f x)‖ + ‖(Real.exp (ψ y) - Real.exp (ψ x)) * f x‖ := norm_add_le _ _
        _ = Real.exp (ψ y) * ‖f y - f x‖ + ‖Real.exp (ψ y) - Real.exp (ψ x)‖ * ‖f x‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp ‖ψ‖ * (Cf * θ ^ (n + 1)) + (Real.exp ‖ψ‖ * (Cψ * θ ^ (n + 1))) * ‖f‖ :=
          add_le_add (mul_le_mul (Real.exp_le_exp.mpr (ContinuousMap.apply_le_norm ψ y)) observable
            (norm_nonneg _) (Real.exp_pos _).le)
            (mul_le_mul weightBound (f.norm_coe_le_norm _) (norm_nonneg _) (by positivity))
        _ = Real.exp ‖ψ‖ * (Cf + Cψ * ‖f‖) * θ ^ (n + 1) := by ring
    · have edgeB : ¬ R j.val (b.val 0) := by rw [← zero]; exact edgeA
      have memberA : a ∉ {c : FuturePath R | R j.val (c.val 0)} := edgeA
      have memberB : b ∉ {c : FuturePath R | R j.val (c.val 0)} := edgeB
      rw [Set.indicator_of_notMem memberA, Set.indicator_of_notMem memberB, sub_self, norm_zero]
      positivity
  rw [← Real.norm_eq_abs]
  change ‖weightedTransfer ψ f b - weightedTransfer ψ f a‖ ≤ _
  dsimp only [weightedTransfer]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : AdmittedSymbol R, ‖{c : FuturePath R | R j.val (c.val 0)}.indicator
          (fun c => Real.exp (ψ (prependOrStay j c)) * f (prependOrStay j c)) b -
        {c : FuturePath R | R j.val (c.val 0)}.indicator
          (fun c => Real.exp (ψ (prependOrStay j c)) * f (prependOrStay j c)) a‖ := norm_sum_le _ _
    _ ≤ ∑ _j : AdmittedSymbol R, Real.exp ‖ψ‖ * (Cf + Cψ * ‖f‖) * θ ^ (n + 1) :=
      Finset.sum_le_sum (fun j _ => term j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_succ]; ring

theorem weightedTransfer_hasExponentialVariations (ψ f : C(FuturePath R, ℝ))
    (variationψ : HasExponentialPrefixVariations ψ)
    (variationF : HasExponentialPrefixVariations f) :
    HasExponentialPrefixVariations (weightedTransfer ψ f) := by
  obtain ⟨θψ, positiveψ, smallψ, Cψ, nonnegativeψ, boundψ⟩ := variationψ
  obtain ⟨θf, positiveF, smallF, Cf, nonnegativeF, boundF⟩ := variationF
  let θ := max θψ θf
  have positive : 0 < θ := lt_of_lt_of_le positiveψ (le_max_left _ _)
  have small : θ < 1 := max_lt smallψ smallF
  refine ⟨θ, positive, small,
    (Fintype.card (AdmittedSymbol R) : ℝ) * Real.exp ‖ψ‖ * θ * (Cf + Cψ * ‖f‖),
    by positivity, ?_⟩
  apply weightedTransfer_variation_bound ψ f θ Cψ Cf positive.le nonnegativeψ nonnegativeF
  · intro n a b same
    exact (boundψ n a b same).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ positiveψ.le (le_max_left _ _) _) nonnegativeψ)
  · intro n a b same
    exact (boundF n a b same).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ positiveF.le (le_max_right _ _) _) nonnegativeF)

end LeanShared.BilateralShadowingCoding
