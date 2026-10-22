module

public import LeanShared.Dynamics.OneSidedPrefixOrbitDistortion
public import LeanShared.Analysis.ExponentialRelativeDistortion

/-! Whole n+m prefix agreement yields a uniform relative weight error
of order θ^m and a uniform two-sided multiplicative weight comparison.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

theorem prefix_orbit_weight_relative_distortion (ψ : FuturePath R → ℝ) (θ Cψ : ℝ)
    (nonnegativeθ : 0 ≤ θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ k a b, PrefixAgreement a b k → |ψ b - ψ a| ≤ Cψ * θ ^ k)
    (n m : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b (n + m)) :
    |Real.exp (orbitSum futureShift ψ n b) - Real.exp (orbitSum futureShift ψ n a)| ≤
      Real.exp (orbitSum futureShift ψ n a) *
        (Real.exp (Cψ * θ / (1 - θ)) * (Cψ * θ / (1 - θ))) * θ ^ m := by
  exact ExponentialRelativeDistortion.bound _ _ _ _
    (div_nonneg (mul_nonneg nonnegativeψ nonnegativeθ) (sub_pos.mpr smallθ).le)
    (pow_nonneg nonnegativeθ m) (pow_le_one₀ nonnegativeθ smallθ.le)
    (prefix_orbit_energy_distortion ψ θ Cψ nonnegativeθ smallθ nonnegativeψ potential n m a b same)

theorem prefix_orbit_weight_comparison (ψ : FuturePath R → ℝ) (θ Cψ : ℝ)
    (nonnegativeθ : 0 ≤ θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ k a b, PrefixAgreement a b k → |ψ b - ψ a| ≤ Cψ * θ ^ k)
    (n m : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b (n + m)) :
    Real.exp (orbitSum futureShift ψ n b) ≤
      Real.exp (Cψ * θ / (1 - θ)) * Real.exp (orbitSum futureShift ψ n a) := by
  let E := Cψ * θ / (1 - θ)
  have nonnegativeE : 0 ≤ E := div_nonneg (mul_nonneg nonnegativeψ nonnegativeθ) (sub_pos.mpr smallθ).le
  have difference := prefix_orbit_energy_distortion ψ θ Cψ nonnegativeθ smallθ nonnegativeψ potential n m a b same
  have bounded : E * θ ^ m ≤ E := mul_le_of_le_one_right nonnegativeE (pow_le_one₀ nonnegativeθ smallθ.le)
  have upper : orbitSum futureShift ψ n b ≤ E + orbitSum futureShift ψ n a := by
    linarith [le_abs_self (orbitSum futureShift ψ n b - orbitSum futureShift ψ n a)]
  simpa only [Real.exp_add] using Real.exp_le_exp.mpr upper

end LeanShared.BilateralShadowingCoding
