module

public import LeanShared.Dynamics.OneSidedWeightedTransfer
public import LeanShared.Dynamics.OneSidedExponentialPotential

/-! A genuine invariant logarithmic cylinder cone for the literal
weighted transfer.  In particular, all iterates of the constant one
have distortion controlled independently of the iterate length.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [Fintype A] {R : A → A → Prop}

@[expose] def PrefixRatioBound (f : FuturePath R → ℝ) (θ K : ℝ) : Prop :=
  ∀ n a b, PrefixAgreement a b n → f b ≤ Real.exp (K * θ ^ n) * f a

theorem weightedTransfer_ratio_bound (ψ f : FuturePath R → ℝ) (θ Cψ K : ℝ)
    (nonnegativeθ : 0 ≤ θ) (invariant : θ * (Cψ + K) ≤ K)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (positiveF : ∀ a, 0 ≤ f a) (ratio : PrefixRatioBound f θ K) :
    PrefixRatioBound (weightedTransfer ψ f) θ K := by
  classical
  intro n a b same
  dsimp only [weightedTransfer]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have zero := same 0 (by omega)
  by_cases edgeA : R j.val (a.val 0)
  · have edgeB : R j.val (b.val 0) := by rw [← zero]; exact edgeA
    have memberA : a ∈ {c : FuturePath R | R j.val (c.val 0)} := edgeA
    have memberB : b ∈ {c : FuturePath R | R j.val (c.val 0)} := edgeB
    rw [Set.indicator_of_mem memberA, Set.indicator_of_mem memberB]
    have prependA : prependOrStay j a = futurePrepend j a edgeA := by
      simp only [prependOrStay, dite_eq_left edgeA]
    have prependB : prependOrStay j b = futurePrepend j b edgeB := by
      simp only [prependOrStay, dite_eq_left edgeB]
    rw [prependA, prependB]
    let x := futurePrepend j a edgeA
    let y := futurePrepend j b edgeB
    have prefixSame := futurePrepend_prefix j a b edgeA edgeB n same
    have comparison : ψ y ≤ ψ x + Cψ * θ ^ (n + 1) := by
      have h := (le_abs_self (ψ y - ψ x)).trans (potential (n + 1) x y prefixSame)
      linarith
    have coefficient : (Cψ + K) * θ ^ (n + 1) ≤ K * θ ^ n := by
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right invariant (pow_nonneg nonnegativeθ n)]
    have exponent : ψ y + K * θ ^ (n + 1) ≤ ψ x + K * θ ^ n := by nlinarith
    calc
      _ ≤ Real.exp (ψ y) * (Real.exp (K * θ ^ (n + 1)) * f x) :=
        mul_le_mul_of_nonneg_left (ratio (n + 1) x y prefixSame) (Real.exp_pos _).le
      _ = Real.exp (ψ y + K * θ ^ (n + 1)) * f x := by rw [Real.exp_add]; ring
      _ ≤ Real.exp (ψ x + K * θ ^ n) * f x :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr exponent) (positiveF x)
      _ = Real.exp (K * θ ^ n) * (Real.exp (ψ x) * f x) := by rw [Real.exp_add]; ring
  · have edgeB : ¬ R j.val (b.val 0) := by rw [← zero]; exact edgeA
    have memberA : a ∉ {c : FuturePath R | R j.val (c.val 0)} := edgeA
    have memberB : b ∉ {c : FuturePath R | R j.val (c.val 0)} := edgeB
    rw [Set.indicator_of_notMem memberA, Set.indicator_of_notMem memberB, mul_zero]

theorem weightedTransfer_iterate_one_nonnegative (ψ : FuturePath R → ℝ) (m : ℕ) :
    ∀ a, 0 ≤ ((weightedTransfer ψ)^[m] (fun _ => 1)) a := by
  induction m with
  | zero => intro a; exact zero_le_one
  | succ m induction =>
    rw [iterate_succ_apply']
    exact weightedTransfer_nonnegative ψ _ induction

theorem weightedTransfer_iterate_one_ratio (ψ : FuturePath R → ℝ) (θ Cψ : ℝ)
    (nonnegativeθ : 0 ≤ θ) (small : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (m : ℕ) :
    PrefixRatioBound ((weightedTransfer ψ)^[m] (fun _ => 1)) θ (Cψ * θ / (1 - θ)) := by
  let K := Cψ * θ / (1 - θ)
  have nonnegativeK : 0 ≤ K := div_nonneg (mul_nonneg nonnegativeψ nonnegativeθ) (sub_pos.mpr small).le
  have invariant : θ * (Cψ + K) ≤ K := by
    dsimp only [K]
    apply le_of_eq
    field_simp [ne_of_gt (sub_pos.mpr small)]
    ring
  induction m with
  | zero =>
    intro n a b _same
    change 1 ≤ Real.exp (K * θ ^ n) * 1
    rw [mul_one]
    exact Real.one_le_exp (mul_nonneg nonnegativeK (pow_nonneg nonnegativeθ n))
  | succ m induction =>
    rw [iterate_succ_apply']
    exact weightedTransfer_ratio_bound ψ _ θ Cψ K nonnegativeθ invariant potential
      (weightedTransfer_iterate_one_nonnegative ψ m) induction

end LeanShared.BilateralShadowingCoding
