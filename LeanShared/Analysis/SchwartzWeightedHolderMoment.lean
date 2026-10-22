module
public import LeanShared.Analysis.SchwartzHolderMoments

/-! Every polynomially weighted fractional absolute Schwartz moment is finite. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace LeanShared.SchwartzHolderMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem polynomial_integrable (k : 𝓢(E,ℂ)) {a R : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hR : 0 ≤ R) (m : ℕ) :
    Integrable (fun y => ‖k y‖ * ‖y‖^a * (1+R+‖y‖)^m) μ := by
  let C : ℝ := (2+R)^m
  have scalar (t : ℝ) (ht : 0 ≤ t) : t^a*(1+R+t)^m ≤ C*(1+t^(m+1)) := by
    by_cases small : t ≤ 1
    · have fractional := Real.rpow_le_one ht small ha.le
      have polynomial : (1+R+t)^m ≤ C :=
        pow_le_pow_left₀ (by positivity) (by linarith) m
      have nn : 0 ≤ (1+R+t)^m := by positivity
      calc
        _ ≤ 1*C := mul_le_mul fractional polynomial nn (by positivity)
        _ ≤ _ := by dsimp [C]; nlinarith [pow_nonneg ht (m+1), pow_nonneg (by linarith : 0≤2+R) m]
    · have large : 1 ≤ t := le_of_not_ge small
      have fractional : t^a ≤ t := (Real.rpow_le_rpow_of_exponent_le large ha1).trans_eq (Real.rpow_one t)
      have base : 1+R+t ≤ (2+R)*t := by nlinarith
      have polynomial := pow_le_pow_left₀ (by positivity : 0≤1+R+t) base m
      calc
        _ ≤ t*((2+R)*t)^m := mul_le_mul fractional polynomial (by positivity) ht
        _ = C*t^(m+1) := by dsimp [C]; rw [mul_pow,pow_succ]; ring
        _ ≤ _ := by dsimp [C]; nlinarith [pow_nonneg (by linarith : 0≤2+R) m]
  have major := ((k.integrable (μ := μ)).norm.add (k.integrable_pow_mul μ (m+1))).const_mul C
  apply major.mono'
  · exact ((k.continuous.norm.mul (continuous_norm.rpow_const (fun _ => Or.inr ha.le))).mul
      ((continuous_const.add continuous_norm).pow m)).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have estimate := mul_le_mul_of_nonneg_left (scalar ‖y‖ (norm_nonneg _)) (norm_nonneg (k y))
    change ‖k y‖ * ‖y‖^a * (1+R+‖y‖)^m ≤ C*(‖k y‖ + ‖y‖^(m+1)*‖k y‖)
    nlinarith only [estimate]
end LeanShared.SchwartzHolderMoments
