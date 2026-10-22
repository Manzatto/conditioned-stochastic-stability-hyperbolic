module

public import LeanShared.Dynamics.OneSidedCylinderDiagonalLoops
public import LeanShared.Dynamics.OneSidedPrefixWeightDistortion

/-! Literal periodic weight sums and actual cylinder-loop weight sums
have uniform multiplicative comparison and exponentially small relative
error in the cylinder window.  The exact periodic-loop bijection is used.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
variable {A : Type*} [TopologicalSpace A] [Fintype A] {R : A → A → Prop}

@[expose] def futurePeriodicWeightSum (ψ : FuturePath R → ℝ) (n : ℕ) [NeZero n] : ℝ :=
  ∑ p : PeriodicFuture (R := R) n, Real.exp (orbitSum futureShift ψ n p.val)

theorem futurePeriodicWeightSum_nonnegative (ψ : FuturePath R → ℝ) (n : ℕ) [NeZero n] :
    0 ≤ futurePeriodicWeightSum ψ n := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)

theorem futurePeriodicWeightSum_as_loops (ψ : FuturePath R → ℝ) (n m : ℕ) [NeZero n] :
    futurePeriodicWeightSum ψ n =
      ∑ d : CylinderLoop (R := R) n m,
        Real.exp (orbitSum futureShift ψ n (cylinderLoopPeriodic n m (Nat.pos_of_ne_zero (NeZero.ne n)) d).val) :=
  (Equiv.sum_comp (cylinderLoopPeriodicEquiv n m (Nat.pos_of_ne_zero (NeZero.ne n)))
    (fun p : PeriodicFuture (R := R) n => Real.exp (orbitSum futureShift ψ n p.val))).symm

theorem futurePeriodicWeightSum_le_loop_sum (ψ : FuturePath R → ℝ) (θ Cψ : ℝ)
    (nonnegativeθ : 0 ≤ θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ k a b, PrefixAgreement a b k → |ψ b - ψ a| ≤ Cψ * θ ^ k)
    (n m : ℕ) [NeZero n] :
    futurePeriodicWeightSum ψ n ≤ Real.exp (Cψ * θ / (1 - θ)) * cylinderLoopWeightSum ψ n m := by
  rw [futurePeriodicWeightSum_as_loops ψ n m]
  change (∑ d : CylinderLoop (R := R) n m, _) ≤
    Real.exp (Cψ * θ / (1 - θ)) * (∑ d : CylinderLoop (R := R) n m, _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  apply prefix_orbit_weight_comparison ψ θ Cψ nonnegativeθ smallθ nonnegativeψ potential n m
    d.val.2 (cylinderLoopPeriodic n m (Nat.pos_of_ne_zero (NeZero.ne n)) d).val
  exact fun k bound => (cylinderLoopPeriodic_window n m (Nat.pos_of_ne_zero (NeZero.ne n)) d k bound).symm

theorem periodic_loop_relative_error (ψ : FuturePath R → ℝ) (θ Cψ : ℝ)
    (nonnegativeθ : 0 ≤ θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ k a b, PrefixAgreement a b k → |ψ b - ψ a| ≤ Cψ * θ ^ k)
    (n m : ℕ) [NeZero n] :
    |cylinderLoopWeightSum ψ n m - futurePeriodicWeightSum ψ n| ≤
      (Real.exp (Cψ * θ / (1 - θ)) * (Cψ * θ / (1 - θ))) * θ ^ m * futurePeriodicWeightSum ψ n := by
  let E := Cψ * θ / (1 - θ)
  have identity := futurePeriodicWeightSum_as_loops ψ n m
  change |(∑ d : CylinderLoop (R := R) n m, Real.exp (orbitSum futureShift ψ n d.val.2)) - _| ≤ _
  conv_lhs => rw [identity, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d : CylinderLoop (R := R) n m,
        Real.exp (orbitSum futureShift ψ n (cylinderLoopPeriodic n m (Nat.pos_of_ne_zero (NeZero.ne n)) d).val) *
          (Real.exp E * E) * θ ^ m := by
      apply Finset.sum_le_sum
      intro d _
      exact prefix_orbit_weight_relative_distortion ψ θ Cψ nonnegativeθ smallθ nonnegativeψ potential n m
        (cylinderLoopPeriodic n m (Nat.pos_of_ne_zero (NeZero.ne n)) d).val d.val.2
        (cylinderLoopPeriodic_window n m (Nat.pos_of_ne_zero (NeZero.ne n)) d)
    _ = (futurePeriodicWeightSum ψ n) * (Real.exp E * E) * θ ^ m := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← identity]
    _ = _ := by ring

end LeanShared.BilateralShadowingCoding
