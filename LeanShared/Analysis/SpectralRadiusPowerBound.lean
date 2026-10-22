module

public import LeanShared.Analysis.SpectralRadiusNeumannSeries
public import Mathlib.Topology.Order.LiminfLimsup

/-! A strict spectral-radius bound produces a uniform geometric bound
on all actual algebra powers.  The constant comes from bounded terms
of the actual convergent outer Neumann series.
-/

public noncomputable section
namespace LeanShared.SpectralRadiusPowerBound
open Set Filter
open scoped Topology NNReal ENNReal
variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

theorem exists_geometric_bound (a : B) (r : ℝ) (positiveR : 0 < r)
    (radiusBound : spectralRadius ℂ a < ENNReal.ofReal r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * r ^ n := by
  have outside : spectralRadius ℂ a < (‖(r : ℂ)‖₊ : ℝ≥0∞) := by
    have normR : ‖(r : ℂ)‖₊ = NNReal.mk r positiveR.le := by
      apply NNReal.eq
      change ‖(r : ℂ)‖ = r
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos positiveR]
    rw [normR]
    simpa only [ENNReal.ofReal_eq_coe_nnreal positiveR.le] using radiusBound
  let term (n : ℕ) : B := (r : ℂ)⁻¹ • ((r : ℂ)⁻¹ • a) ^ n
  have convergence : Tendsto (fun n => ‖term n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using ((SpectralRadiusNeumannSeries.hasSum a (r : ℂ) outside).summable.tendsto_atTop_zero).norm
  obtain ⟨M, bound⟩ := convergence.isBoundedUnder_le.bddAbove_range
  let K := max 1 M
  have positiveK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨r * K, mul_pos positiveR positiveK, ?_⟩
  intro n
  have termBound : ‖term n‖ ≤ K := (bound (mem_range_self n)).trans (le_max_right _ _)
  have rescaling : ‖a ^ n‖ = r ^ (n + 1) * ‖term n‖ := by
    dsimp only [term]
    rw [norm_smul, smul_pow, norm_smul, norm_pow ((r : ℂ)⁻¹) n]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positiveR]
    rw [pow_succ]
    calc
      ‖a ^ n‖ = ((r * r⁻¹) * (r ^ n * r⁻¹ ^ n)) * ‖a ^ n‖ := by
        rw [← mul_pow, mul_inv_cancel₀ positiveR.ne', one_pow, one_mul, one_mul]
      _ = _ := by ring
  calc
    _ = r ^ (n + 1) * ‖term n‖ := rescaling
    _ ≤ r ^ (n + 1) * K := mul_le_mul_of_nonneg_left termBound (pow_nonneg positiveR.le _)
    _ = (r * K) * r ^ n := by rw [pow_succ]; ring

theorem exists_geometric_bound_of_spectrum (a : B) (q r : ℝ) (positiveR : 0 < r)
    (gap : q < r) (bound : ∀ z ∈ spectrum ℂ a, ‖z‖ ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * r ^ n := by
  rcases subsingleton_or_nontrivial B with trivial | nontrivial
  · have := trivial
    exact ⟨1, zero_lt_one, fun n => by simp only [Subsingleton.elim (a ^ n) 0, norm_zero, one_mul]; positivity⟩
  · have := nontrivial
    have radiusBound : spectralRadius ℂ a < ENNReal.ofNNReal (NNReal.mk r positiveR.le) :=
      spectrum.spectralRadius_lt_of_forall_lt a (fun z member => by
        exact_mod_cast (bound z member).trans_lt gap)
    apply exists_geometric_bound a r positiveR
    simpa only [ENNReal.ofReal_eq_coe_nnreal positiveR.le] using radiusBound

end LeanShared.SpectralRadiusPowerBound
