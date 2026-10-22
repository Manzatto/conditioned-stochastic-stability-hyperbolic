module

public import LeanShared.Analysis.FiniteExponentialDeterminant

/-! A literal exponential zeta series whose coefficients equal lambda^n
up to a strictly smaller exponential has a nonzero analytic numerator
beyond its leading pole.  All series and factors are explicitly defined.
-/

public noncomputable section
namespace LeanShared.ExponentiallyAccurateZeta
open ExponentialCoefficientSeries
open scoped NNReal ENNReal

@[expose] def zeta (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (∑' n, a n / (n : ℂ) * z ^ n)

theorem zeta_eq_inverse (a : ℕ → ℂ) (z : ℂ) : zeta a z = (correction a z)⁻¹ := by
  have terms : (fun n => a n / (n : ℂ) * z ^ n) =
      -(fun n => logarithmicCoefficient a n * z ^ n) := by
    funext n
    dsimp [logarithmicCoefficient]
    ring
  rw [zeta, correction, terms]
  change Complex.exp (∑' n, -(logarithmicCoefficient a n * z ^ n)) = _
  rw [tsum_neg, Complex.exp_neg]

theorem factor (a : ℕ → ℂ) (ρ κ D : ℝ) (positiveρ : 0 < ρ)
    (positiveκ : 0 < κ) (smallκ : κ < 1)
    (bound : ∀ n, ‖a n - (ρ : ℂ) ^ n‖ ≤ D * (ρ * κ) ^ n) :
    ∃ r : ℝ≥0, 1 / ρ < (r : ℝ) ∧ ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (Metric.eball 0 (r : ℝ≥0∞)) ∧ H 0 = 1 ∧
      (∀ z, H z ≠ 0) ∧ ∀ z : ℂ, ρ * ‖z‖ < 1 →
        zeta a z = H z / (1 - (ρ : ℂ) * z) := by
  let q : ℝ≥0 := NNReal.mk (ρ * κ) (by positivity)
  let r : ℝ≥0 := NNReal.mk (((1 + κ⁻¹) / 2) / ρ) (by positivity)
  let d := fun n => a n - (ρ : ℂ) ^ n
  let H := fun z => (correction d z)⁻¹
  have rlarge : 1 / ρ < (r : ℝ) := by
    have larger := (one_lt_inv₀ positiveκ).mpr smallκ
    change 1 / ρ < ((1 + κ⁻¹) / 2) / ρ
    exact div_lt_div_of_pos_right (by linarith) positiveρ
  have smallRadius : q * r ≤ 1 := by
    change (ρ * κ) * (((1 + κ⁻¹) / 2) / ρ) ≤ 1
    have algebra : (ρ * κ) * (((1 + κ⁻¹) / 2) / ρ) = (κ + 1) / 2 := by
      field_simp
    rw [algebra]
    linarith
  have analyticH : AnalyticOnNhd ℂ H (Metric.eball 0 (r : ℝ≥0∞)) :=
    (correction_analytic d D q r bound smallRadius).inv (fun z _ => correction_ne_zero d z)
  refine ⟨r, rlarge, H, analyticH, ?_, ?_, ?_⟩
  · dsimp [H]
    rw [correction_zero, inv_one]
  · intro z
    exact inv_ne_zero (correction_ne_zero d z)
  · intro z small
    let l : ℝ≥0 := NNReal.mk ρ positiveρ.le
    have baseBound (n : ℕ) : ‖(ρ : ℂ) ^ n‖ ≤ 1 * (l : ℝ) ^ n := by
      simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positiveρ,
        one_mul, NNReal.coe_mk, l, le_refl]
    have baseSummable := summable_logarithmic (fun n => (ρ : ℂ) ^ n) 1 l baseBound z small
    have errorSmall : (q : ℝ) * ‖z‖ < 1 := by
      have estimate := mul_le_mul_of_nonneg_right smallκ.le (mul_nonneg positiveρ.le (norm_nonneg z))
      change (ρ * κ) * ‖z‖ < 1
      nlinarith
    have errorSummable := summable_logarithmic d D q bound z errorSmall
    have allSummable : Summable (fun n => logarithmicCoefficient a n * z ^ n) := by
      convert errorSummable.add baseSummable using 1
      funext n
      dsimp [d, logarithmicCoefficient]
      ring
    have baseFactor : correction (fun n => (ρ : ℂ) ^ n) z = 1 - (ρ : ℂ) * z := by
      have smallComplex : ‖z * (ρ : ℂ)‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positiveρ]
        nlinarith
      have finite := FiniteExponentialDeterminant.correction_eq_product
        (fun _ : Unit => (ρ : ℂ)) z (fun _ => smallComplex)
      simpa only [Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton, mul_comm] using finite
    have exactFactor := determinant_factorization a (fun n => (ρ : ℂ) ^ n) z allSummable baseSummable
    rw [zeta_eq_inverse, exactFactor, baseFactor, mul_inv_rev]
    rfl

end LeanShared.ExponentiallyAccurateZeta
