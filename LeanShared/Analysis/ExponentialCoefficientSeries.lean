module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring

/-! Geometric coefficient errors give a holomorphic correction series on an
explicit disk. This is the scalar analytic step in comparing periodic zeta
and flat determinants. -/

public noncomputable section
open scoped NNReal ENNReal

namespace LeanShared.ExponentialCoefficientSeries

/-- A coefficient estimate gives a convergence disk, including its boundary
as a lower bound for the formal radius. -/
theorem radius_lower (c : ℕ → ℂ) (C : ℝ) (θ r : ℝ≥0)
    (bound : ∀ n, ‖c n‖ ≤ C * (θ : ℝ) ^ n)
    (small : θ * r ≤ 1) :
    (r : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound _ C
  intro n
  rw [FormalMultilinearSeries.ofScalars_norm]
  have positiveC : 0 ≤ C := (norm_nonneg (c 0)).trans (by simpa using bound 0)
  calc
    ‖c n‖ * (r : ℝ) ^ n ≤ (C * (θ : ℝ) ^ n) * (r : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right (bound n) (pow_nonneg r.coe_nonneg n)
    _ = C * ((θ : ℝ) * (r : ℝ)) ^ n := by rw [mul_pow]; ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (mul_nonneg θ.coe_nonneg r.coe_nonneg) (by exact_mod_cast small)) positiveC
    _ = C := mul_one C

/-- The literal scalar sum is analytic throughout every disk certified by
the geometric coefficient estimate. -/
theorem analytic (c : ℕ → ℂ) (C : ℝ) (θ r : ℝ≥0)
    (bound : ∀ n, ‖c n‖ ≤ C * (θ : ℝ) ^ n)
    (small : θ * r ≤ 1) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∑' n, c n * z ^ n)
      (Metric.eball 0 (r : ℝ≥0∞)) := by
  have h := (FormalMultilinearSeries.ofScalars ℂ c).analyticOnNhd.mono
    (Metric.eball_subset_eball (radius_lower c C θ r bound small))
  change AnalyticOnNhd ℂ (FormalMultilinearSeries.ofScalarsSum c)
    (Metric.eball 0 (r : ℝ≥0∞)) at h
  simpa only [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] using h

/-- Coefficients of the difference of the two logarithmic determinants.
Division at zero makes the constant coefficient zero. -/
@[expose] def logarithmicCoefficient (d : ℕ → ℂ) (n : ℕ) : ℂ := -d n / (n : ℂ)

theorem logarithmic_bound (d : ℕ → ℂ) (C : ℝ) (θ : ℝ≥0)
    (bound : ∀ n, ‖d n‖ ≤ C * (θ : ℝ) ^ n) :
    ∀ n, ‖logarithmicCoefficient d n‖ ≤ C * (θ : ℝ) ^ n := by
  intro n
  have positiveC : 0 ≤ C := (norm_nonneg (d 0)).trans (by simpa using bound 0)
  by_cases hn : n = 0
  · simp [logarithmicCoefficient, hn, positiveC]
  · have one : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have normNat : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    calc
      ‖logarithmicCoefficient d n‖ = ‖d n‖ / (n : ℝ) := by
        simp only [logarithmicCoefficient, norm_div, norm_neg, normNat]
      _ ≤ ‖d n‖ := div_le_self (norm_nonneg _) one
      _ ≤ C * (θ : ℝ) ^ n := bound n

/-- The same geometric estimate supplies actual convergence, needed for the
literal exponential-determinant factorization. -/
theorem summable_logarithmic (d : ℕ → ℂ) (C : ℝ) (θ : ℝ≥0)
    (bound : ∀ n, ‖d n‖ ≤ C * (θ : ℝ) ^ n)
    (z : ℂ) (small : (θ : ℝ) * ‖z‖ < 1) :
    Summable (fun n => logarithmicCoefficient d n * z ^ n) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (mul_nonneg θ.coe_nonneg (norm_nonneg z)) small).mul_left C)
  intro n
  calc
    ‖logarithmicCoefficient d n * z ^ n‖ = ‖logarithmicCoefficient d n‖ * ‖z‖ ^ n := by
      rw [norm_mul, norm_pow]
    _ ≤ (C * (θ : ℝ) ^ n) * ‖z‖ ^ n :=
      mul_le_mul_of_nonneg_right (logarithmic_bound d C θ bound n) (pow_nonneg (norm_nonneg z) n)
    _ = C * ((θ : ℝ) * ‖z‖) ^ n := by rw [mul_pow]; ring

/-- The multiplicative determinant correction defined by literal coefficients. -/
@[expose] def correction (d : ℕ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (∑' n, logarithmicCoefficient d n * z ^ n)

theorem correction_analytic (d : ℕ → ℂ) (C : ℝ) (θ r : ℝ≥0)
    (bound : ∀ n, ‖d n‖ ≤ C * (θ : ℝ) ^ n) (small : θ * r ≤ 1) :
    AnalyticOnNhd ℂ (correction d) (Metric.eball 0 (r : ℝ≥0∞)) := by
  intro z hz
  exact analyticAt_cexp.comp (analytic _ C θ r (logarithmic_bound d C θ bound) small z hz)

theorem correction_ne_zero (d : ℕ → ℂ) (z : ℂ) : correction d z ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem correction_zero (d : ℕ → ℂ) : correction d 0 = 1 := by
  have terms (n : ℕ) : logarithmicCoefficient d n * (0 : ℂ) ^ n = 0 := by
    cases n <;> simp [logarithmicCoefficient]
  simp only [correction, terms, tsum_zero, Complex.exp_zero]

/-- On any common convergence disk the correction is exactly the quotient
of the two exponential determinants, with their literal coefficients. -/
theorem correction_sub (a b : ℕ → ℂ) (z : ℂ)
    (ha : Summable (fun n => logarithmicCoefficient a n * z ^ n))
    (hb : Summable (fun n => logarithmicCoefficient b n * z ^ n)) :
    correction (fun n => a n - b n) z = correction a z / correction b z := by
  have terms : (fun n => logarithmicCoefficient (fun k => a k - b k) n * z ^ n) =
      (fun n => logarithmicCoefficient a n * z ^ n) -
        (fun n => logarithmicCoefficient b n * z ^ n) := by
    funext n
    dsimp only [logarithmicCoefficient, Pi.sub_apply]
    ring
  simp only [correction, terms]
  exact (congrArg Complex.exp (ha.tsum_sub hb)).trans (Complex.exp_sub _ _)

/-- Exact factorization on the common disk. The last factor extends to the
larger disk supplied by the coefficient error estimate. -/
theorem determinant_factorization (a b : ℕ → ℂ) (z : ℂ)
    (ha : Summable (fun n => logarithmicCoefficient a n * z ^ n))
    (hb : Summable (fun n => logarithmicCoefficient b n * z ^ n)) :
    correction a z = correction b z * correction (fun n => a n - b n) z := by
  have h := (eq_div_iff (correction_ne_zero b z)).mp (correction_sub a b z ha hb)
  simpa only [mul_comm] using h.symm

end LeanShared.ExponentialCoefficientSeries
