module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity

/-! Genuine exponential stable/inverse bounds yield a fixed strict
exponential principal multiplier for every positive/negative exponent pair. -/
public section
namespace LeanShared.ExponentialPrincipalFactor

theorem bound (A q t u stable inverse : ℝ) (N : ℕ)
    (nonnegativeA : 0 ≤ A) (nonnegativeq : 0 ≤ q) (nonnegativeT : 0 ≤ t) (nonnegativeU : 0 ≤ u)
    (nonnegativeStable : 0 ≤ stable) (nonnegativeInverse : 0 ≤ inverse)
    (stableBound : stable ≤ A*q^N) (inverseBound : inverse ≤ A*q^N) :
    max (stable^t) (inverse^u) ≤ max (A^t) (A^u)*(max (q^t) (q^u))^N := by
  have estimate (v e : ℝ) (nonnegativeV : 0 ≤ v) (nonnegativeE : 0 ≤ e)
      (boundV : v ≤ A*q^N) (boundA : A^e ≤ max (A^t) (A^u))
      (boundQ : q^e ≤ max (q^t) (q^u)) :
      v^e ≤ max (A^t) (A^u)*(max (q^t) (q^u))^N := by
    calc
      _  ≤  (A*q^N)^e := Real.rpow_le_rpow nonnegativeV boundV nonnegativeE
      _ = A^e*(q^e)^N := by rw [Real.mul_rpow nonnegativeA (pow_nonneg nonnegativeq N),←Real.rpow_pow_comm nonnegativeq]
      _  ≤  _ := mul_le_mul boundA (pow_le_pow_left₀ (Real.rpow_nonneg nonnegativeq e) boundQ N)
        (pow_nonneg (Real.rpow_nonneg nonnegativeq e) N)
        ((Real.rpow_nonneg nonnegativeA t).trans (le_max_left _ _))
  exact max_le (estimate stable t nonnegativeStable nonnegativeT stableBound (le_max_left _ _) (le_max_left _ _))
    (estimate inverse u nonnegativeInverse nonnegativeU inverseBound (le_max_right _ _) (le_max_right _ _))

theorem rate_positive_lt_one {q t u : ℝ} (positiveq : 0<q) (smallq : q<1)
    (positiveT : 0<t) (positiveU : 0<u) : 0<max (q^t) (q^u) ∧ max (q^t) (q^u)<1 :=
  ⟨(Real.rpow_pos_of_pos positiveq t).trans_le (le_max_left _ _),
    max_lt (Real.rpow_lt_one positiveq.le smallq positiveT) (Real.rpow_lt_one positiveq.le smallq positiveU)⟩
end LeanShared.ExponentialPrincipalFactor
