module

public import LeanShared.Dynamics.OneSidedNormalizedTransfer
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The positive eigenfunction normalizes the literal weighted transfer
by an explicit logarithmic coboundary.  The potential, its exponential
weights and the unital operator identity are actual constructions.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

@[expose] def eigenfunctionLog (h : C(FuturePath R, ℝ)) (positiveH : ∀ a, 0 < h a) :
    C(FuturePath R, ℝ) :=
  ⟨fun a => Real.log (h a), h.continuous.log (fun a => (positiveH a).ne')⟩

@[expose] def normalizedPotential (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveH : ∀ a, 0 < h a) : C(FuturePath R, ℝ) :=
  ψ + eigenfunctionLog h positiveH -
    (eigenfunctionLog h positiveH).comp ⟨futureShift, futureShift_continuous⟩ -
      ContinuousMap.const _ (Real.log eigenvalue)

omit [DiscreteTopology A] [CompactSpace A] [Fintype A] in
theorem normalizedPotential_exp (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveEigenvalue : 0 < eigenvalue) (positiveH : ∀ a, 0 < h a) (a : FuturePath R) :
    Real.exp (normalizedPotential ψ h eigenvalue positiveH a) =
      Real.exp (ψ a) * h a / (eigenvalue * h (futureShift a)) := by
  change Real.exp (ψ a + Real.log (h a) - Real.log (h (futureShift a)) - Real.log eigenvalue) = _
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log (positiveH a),
    Real.exp_log (positiveH (futureShift a)), Real.exp_log positiveEigenvalue]
  ring

theorem weightedTransfer_normalizedPotential (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveEigenvalue : 0 < eigenvalue) (positiveH : ∀ a, 0 < h a) :
    weightedTransferOperator (normalizedPotential ψ h eigenvalue positiveH) =
      normalizedTransferOperator ψ h eigenvalue positiveEigenvalue positiveH := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousMap.ext
  intro a
  rw [normalizedTransferOperator_apply]
  change weightedTransfer (normalizedPotential ψ h eigenvalue positiveH) f a =
    (eigenvalue * h a)⁻¹ * weightedTransfer ψ (h * f) a
  dsimp only [weightedTransfer]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases edge : R j.val (a.val 0)
  · have member : a ∈ {b : FuturePath R | R j.val (b.val 0)} := edge
    rw [Set.indicator_of_mem member, Set.indicator_of_mem member,
      normalizedPotential_exp ψ h eigenvalue positiveEigenvalue positiveH]
    have shiftBack : futureShift (prependOrStay j a) = a := by
      rw [prependOrStay, dite_eq_left edge]
      exact futureShift_prepend j a edge
    rw [shiftBack]
    change Real.exp (ψ (prependOrStay j a)) * h (prependOrStay j a) /
      (eigenvalue * h a) * f (prependOrStay j a) =
      (eigenvalue * h a)⁻¹ * (Real.exp (ψ (prependOrStay j a)) *
        (h (prependOrStay j a) * f (prependOrStay j a)))
    ring
  · have member : a ∉ {b : FuturePath R | R j.val (b.val 0)} := edge
    rw [Set.indicator_of_notMem member, Set.indicator_of_notMem member, mul_zero]

theorem normalizedPotential_unital (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveEigenvalue : 0 < eigenvalue) (positiveH : ∀ a, 0 < h a)
    (eigen : weightedTransferOperator ψ h = eigenvalue • h) :
    weightedTransferOperator (normalizedPotential ψ h eigenvalue positiveH) 1 = 1 := by
  rw [weightedTransfer_normalizedPotential ψ h eigenvalue positiveEigenvalue positiveH]
  exact normalizedTransferOperator_one ψ h eigenvalue positiveEigenvalue positiveH eigen

omit [DiscreteTopology A] [CompactSpace A] [Fintype A] in
theorem eigenfunctionLog_variation (h : C(FuturePath R, ℝ)) (positiveH : ∀ a, 0 < h a)
    (θ K : ℝ) (ratio : PrefixRatioBound h θ K) (n : ℕ) (a b : FuturePath R)
    (same : PrefixAgreement a b n) :
    |eigenfunctionLog h positiveH b - eigenfunctionLog h positiveH a| ≤ K * θ ^ n := by
  have upper (x y : FuturePath R) (matching : PrefixAgreement x y n) :
      Real.log (h y) - Real.log (h x) ≤ K * θ ^ n := by
    have comparison := Real.log_le_log (positiveH y) (ratio n x y matching)
    rw [Real.log_mul (Real.exp_pos _).ne' (positiveH x).ne', Real.log_exp] at comparison
    linarith
  change |Real.log (h b) - Real.log (h a)| ≤ K * θ ^ n
  exact abs_le.mpr ⟨by linarith [upper b a (fun k hk => (same k hk).symm)], upper a b same⟩

omit [Fintype A] in
theorem futureShift_prefix_variation (f : C(FuturePath R, ℝ)) (θ C : ℝ)
    (positiveθ : 0 < θ) (nonnegativeC : 0 ≤ C)
    (variation : ∀ n a b, PrefixAgreement a b n → |f b - f a| ≤ C * θ ^ n)
    (n : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b n) :
    |f (futureShift b) - f (futureShift a)| ≤ (2 * ‖f‖ + C / θ) * θ ^ n := by
  cases n with
  | zero =>
    have bound : |f (futureShift b) - f (futureShift a)| ≤ 2 * ‖f‖ := by
      calc
        _ ≤ |f (futureShift b)| + |f (futureShift a)| := abs_sub _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
        _ = _ := by ring
    simpa only [pow_zero, mul_one] using
      bound.trans (le_add_of_nonneg_right (div_nonneg nonnegativeC positiveθ.le))
  | succ n =>
    have matching : PrefixAgreement (futureShift a) (futureShift b) n :=
      fun k bound => same (k + 1) (by omega)
    calc
      _ ≤ C * θ ^ n := variation n _ _ matching
      _ = (C / θ) * θ ^ (n + 1) := by rw [pow_succ]; field_simp
      _ ≤ (2 * ‖f‖ + C / θ) * θ ^ (n + 1) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (pow_nonneg positiveθ.le _)

omit [Fintype A] in
theorem normalizedPotential_variation (ψ h : C(FuturePath R, ℝ)) (eigenvalue θ Cψ K : ℝ)
    (positiveH : ∀ a, 0 < h a) (positiveθ : 0 < θ) (nonnegativeK : 0 ≤ K)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (ratio : PrefixRatioBound h θ K) (n : ℕ) (a b : FuturePath R)
    (same : PrefixAgreement a b n) :
    |normalizedPotential ψ h eigenvalue positiveH b - normalizedPotential ψ h eigenvalue positiveH a| ≤
      (Cψ + K + (2 * ‖eigenfunctionLog h positiveH‖ + K / θ)) * θ ^ n := by
  have logVariation := eigenfunctionLog_variation h positiveH θ K ratio
  have shiftVariation := futureShift_prefix_variation (eigenfunctionLog h positiveH) θ K
    positiveθ nonnegativeK logVariation n a b same
  have identity : normalizedPotential ψ h eigenvalue positiveH b -
      normalizedPotential ψ h eigenvalue positiveH a =
      (ψ b - ψ a) + (eigenfunctionLog h positiveH b - eigenfunctionLog h positiveH a) -
        (eigenfunctionLog h positiveH (futureShift b) - eigenfunctionLog h positiveH (futureShift a)) := by
    change (ψ b + Real.log (h b) - Real.log (h (futureShift b)) - Real.log eigenvalue) -
      (ψ a + Real.log (h a) - Real.log (h (futureShift a)) - Real.log eigenvalue) = _
    change _ = (ψ b - ψ a) + (Real.log (h b) - Real.log (h a)) -
      (Real.log (h (futureShift b)) - Real.log (h (futureShift a)))
    ring
  rw [identity]
  calc
    _ ≤ |ψ b - ψ a| + |eigenfunctionLog h positiveH b - eigenfunctionLog h positiveH a| +
        |eigenfunctionLog h positiveH (futureShift b) - eigenfunctionLog h positiveH (futureShift a)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Cψ * θ ^ n + K * θ ^ n + (2 * ‖eigenfunctionLog h positiveH‖ + K / θ) * θ ^ n :=
      add_le_add (add_le_add (potential n a b same) (logVariation n a b same)) shiftVariation
    _ = _ := by ring

end LeanShared.BilateralShadowingCoding
