module

public import LeanShared.Dynamics.OneSidedPeriodicWeightComparison

/-! Quantitative comparison of literal periodic sums to the actual
finite-cylinder diagonal.  The cylinder window can be chosen freely;
the period dependence is supplied by the proved Ruelle power bound.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

theorem realCylinderLoop_error (ψ : C(FuturePath R, ℝ)) (m n : ℕ) (D : ℝ)
    (bound : ‖complexCylinderPowerDiagonal ψ m n - 1‖ ≤ D) :
    |cylinderLoopWeightSum ψ n m - 1| ≤ D := by
  rw [complexCylinderPowerDiagonal_eq_real_loop_sum] at bound
  simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using bound

theorem periodicWeightSum_uniform_bound (ψ : C(FuturePath R, ℝ)) (θ Cψ τ C : ℝ)
    (nonnegativeθ : 0 ≤ θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ k a b, PrefixAgreement a b k → |ψ b - ψ a| ≤ Cψ * θ ^ k)
    (nonnegativeτ : 0 ≤ τ) (smallτ : τ ≤ 1) (nonnegativeC : 0 ≤ C)
    (diagonal : ∀ m n : ℕ, ‖complexCylinderPowerDiagonal ψ m n - 1‖ ≤
      (Fintype.card (RealizedPrefix R m) : ℝ) * (2 * θ⁻¹ ^ m) * C * τ ^ n)
    (n : ℕ) [NeZero n] :
    futurePeriodicWeightSum ψ n ≤
      Real.exp (Cψ * θ / (1 - θ)) * (1 + (Fintype.card (RealizedPrefix R 0) : ℝ) * 2 * C) := by
  have err := realCylinderLoop_error ψ 0 n _ (diagonal 0 n)
  have power := pow_le_one₀ nonnegativeτ smallτ (n := n)
  have finiteBound : (Fintype.card (RealizedPrefix R 0) : ℝ) * 2 * C * τ ^ n ≤
      (Fintype.card (RealizedPrefix R 0) : ℝ) * 2 * C :=
    mul_le_of_le_one_right (by positivity) power
  simp only [pow_zero, mul_one] at err
  have loopBound : cylinderLoopWeightSum ψ n 0 ≤
      1 + (Fintype.card (RealizedPrefix R 0) : ℝ) * 2 * C := by
    have lower := le_abs_self (cylinderLoopWeightSum ψ n 0 - 1)
    linarith
  exact (futurePeriodicWeightSum_le_loop_sum ψ θ Cψ nonnegativeθ smallθ nonnegativeψ potential n 0).trans
    (mul_le_mul_of_nonneg_left loopBound (Real.exp_pos _).le)

theorem periodicWeightSum_window_error (ψ : C(FuturePath R, ℝ)) (θ Cψ τ C K : ℝ)
    (nonnegativeθ : 0 ≤ θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ k a b, PrefixAgreement a b k → |ψ b - ψ a| ≤ Cψ * θ ^ k)
    (diagonal : ∀ m n : ℕ, ‖complexCylinderPowerDiagonal ψ m n - 1‖ ≤
      (Fintype.card (RealizedPrefix R m) : ℝ) * (2 * θ⁻¹ ^ m) * C * τ ^ n)
    (n m : ℕ) [NeZero n] (uniformBound : futurePeriodicWeightSum ψ n ≤ K) :
    |futurePeriodicWeightSum ψ n - 1| ≤
      (Real.exp (Cψ * θ / (1 - θ)) * (Cψ * θ / (1 - θ))) * K * θ ^ m +
        (Fintype.card (RealizedPrefix R m) : ℝ) * (2 * θ⁻¹ ^ m) * C * τ ^ n := by
  have Epos : 0 ≤ Cψ * θ / (1 - θ) := by positivity
  have relative := periodic_loop_relative_error ψ θ Cψ nonnegativeθ smallθ nonnegativeψ potential n m
  have relative' : |futurePeriodicWeightSum ψ n - cylinderLoopWeightSum ψ n m| ≤
      (Real.exp (Cψ * θ / (1 - θ)) * (Cψ * θ / (1 - θ))) * K * θ ^ m := by
    rw [abs_sub_comm] at relative
    apply relative.trans
    calc
      _ ≤ (Real.exp (Cψ * θ / (1 - θ)) * (Cψ * θ / (1 - θ))) * θ ^ m * K :=
        mul_le_mul_of_nonneg_left uniformBound (by positivity)
      _ = _ := by ring
  have triangle := abs_add_le (futurePeriodicWeightSum ψ n - cylinderLoopWeightSum ψ n m)
    (cylinderLoopWeightSum ψ n m - 1)
  have realerr := realCylinderLoop_error ψ m n _ (diagonal m n)
  have joined := add_le_add relative' realerr
  have identity : futurePeriodicWeightSum ψ n - cylinderLoopWeightSum ψ n m +
      (cylinderLoopWeightSum ψ n m - 1) = futurePeriodicWeightSum ψ n - 1 := by ring
  rw [identity] at triangle
  exact triangle.trans joined

end LeanShared.BilateralShadowingCoding
