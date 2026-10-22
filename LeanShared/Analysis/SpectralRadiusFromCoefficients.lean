module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A positive exponential lower bound along any unbounded sequence of
operator powers gives a genuine spectral-radius lower bound by Gelfand's
formula. The sequence may consist of block multiples minus one, as required
when a supported departure weight replaces a constant seed. -/

public noncomputable section
open Filter
open scoped Topology ENNReal

namespace LeanShared.SpectralRadiusFromCoefficients

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem le_spectralRadius_of_subsequence_lower (a : A) (r c : ℝ)
    (hr : 0 ≤ r) (hc : 0 < c) (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lower : ∀ᶠ n in atTop, c * r ^ k n ≤ ‖a ^ k n‖) :
    ENNReal.ofReal r ≤ spectralRadius ℂ a := by
  have rootLimit : Tendsto (fun n : ℕ => c ^ (1 / (k n : ℝ))) atTop (𝓝 (1 : ℝ)) := by
    have h := ((Real.continuousAt_const_rpow (ne_of_gt hc)).tendsto).comp
      ((tendsto_const_div_atTop_nhds_zero_nat 1).comp hk)
    simpa only [Real.rpow_zero, Function.comp_def] using h
  have leftLimit := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (rootLimit.mul (tendsto_const_nhds (x := r)))
  have rightLimit := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a).comp hk
  apply le_of_tendsto_of_tendsto (by simpa only [one_mul] using leftLimit) rightLimit
  filter_upwards [lower, hk.eventually (eventually_ge_atTop 1)] with n hn hkn
  have positiveK : 0 < (k n : ℝ) := by exact_mod_cast hkn
  have rootIdentity : (c * r ^ k n) ^ (1 / (k n : ℝ)) =
      c ^ (1 / (k n : ℝ)) * r := by
    rw [Real.mul_rpow hc.le (pow_nonneg hr _), ← Real.rpow_natCast,
      ← Real.rpow_mul hr, mul_one_div_cancel positiveK.ne', Real.rpow_one]
  apply ENNReal.ofReal_le_ofReal
  change c ^ (1 / (k n : ℝ)) * r ≤ ‖a ^ k n‖ ^ (1 / (k n : ℝ))
  rw [← rootIdentity]
  exact Real.rpow_le_rpow (mul_nonneg hc.le (pow_nonneg hr _)) hn
    (one_div_nonneg.mpr positiveK.le)

/-- A continuous matrix coefficient supplies the lower norm bound. The
normalization uses a positive bound even if the functional or vector is zero;
in that case a positive lower-growth hypothesis is itself impossible. -/
theorem le_spectralRadius_of_matrixCoefficient_lower
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (P : B →L[ℂ] B) (pairing : B →L[ℂ] ℂ) (seed : B)
    (r c : ℝ) (hr : 0 ≤ r) (hc : 0 < c)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lower : ∀ᶠ n in atTop, c * r ^ k n ≤ ‖pairing ((P ^ k n) seed)‖) :
    ENNReal.ofReal r ≤ spectralRadius ℂ P := by
  let D := max 1 (‖pairing‖ * ‖seed‖)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply le_spectralRadius_of_subsequence_lower P r (c / D) hr (div_pos hc hD) k hk
  filter_upwards [lower] with n hn
  have coefficientBound : ‖pairing ((P ^ k n) seed)‖ ≤ D * ‖P ^ k n‖ := by
    calc
      _ ≤ ‖pairing‖ * ‖(P ^ k n) seed‖ := pairing.le_opNorm _
      _ ≤ ‖pairing‖ * (‖P ^ k n‖ * ‖seed‖) :=
        mul_le_mul_of_nonneg_left ((P ^ k n).le_opNorm _) (norm_nonneg _)
      _ = (‖pairing‖ * ‖seed‖) * ‖P ^ k n‖ := by ring
      _ ≤ D * ‖P ^ k n‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  have scaled := (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hn.trans coefficientBound)
  simpa only [div_mul_eq_mul_div] using scaled

/-- Block growth with an arbitrarily small exponent loss proves the full
pressure lower bound. The one-step shift is the weight-seed shift, and the
block length and constant may depend on the requested loss. -/
theorem exp_le_spectralRadius_of_shifted_block_growth
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (T : B →L[ℂ] B) (pairing : B →L[ℂ] ℂ) (seed : B) (P : ℝ)
    (growth : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ p : ℕ, 0 < p → Real.exp ((N * p : ℕ) * (P - δ)) ≤
        C * ‖pairing ((T ^ (N * p - 1)) seed)‖) :
    ENNReal.ofReal (Real.exp P) ≤ spectralRadius ℂ T := by
  have lower (δ : ℝ) (hδ : 0 < δ) :
      ENNReal.ofReal (Real.exp (P - δ)) ≤ spectralRadius ℂ T := by
    obtain ⟨N, hN, C, hC, bound⟩ := growth δ hδ
    let k := fun p : ℕ => N * (p + 1) - 1
    have hk : Tendsto k atTop atTop := by
      apply tendsto_atTop_mono (f := fun p : ℕ => p) _ tendsto_id
      intro p
      have hmul : p + 1 ≤ N * (p + 1) := by
        calc
          p + 1 = 1 * (p + 1) := (one_mul _).symm
          _ ≤ N * (p + 1) := Nat.mul_le_mul_right (p + 1) hN
      dsimp only [k]
      omega
    apply le_spectralRadius_of_matrixCoefficient_lower T pairing seed
      (Real.exp (P - δ)) (Real.exp (P - δ) / C) (Real.exp_pos _).le
      (div_pos (Real.exp_pos _) hC) k hk
    apply Filter.Eventually.of_forall
    intro p
    have h := bound (p + 1) (Nat.succ_pos p)
    have hNpos : 0 < N * (p + 1) := Nat.mul_pos hN (Nat.succ_pos p)
    have hk1 : k p + 1 = N * (p + 1) := Nat.sub_add_cancel hNpos
    rw [Real.exp_nat_mul, ← hk1, pow_succ] at h
    have scaled := (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using h)
    simpa only [div_mul_eq_mul_div, mul_comm, Nat.add_sub_cancel] using scaled
  have lossLimit : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat 1)
  have exponentLimit : Tendsto (fun n : ℕ => P - 1 / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 P) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := P)).sub lossLimit
  have expLimit := Real.continuous_exp.continuousAt.tendsto.comp exponentLimit
  have limit : Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.exp (P - 1 / ((n + 1 : ℕ) : ℝ)))) atTop (𝓝 (ENNReal.ofReal (Real.exp P))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp expLimit
  apply le_of_tendsto limit
  exact Filter.Eventually.of_forall (fun n => lower _ (by positivity))

/-- Convert the geometric weighted-integral estimate (with its blockwise
`γ` loss and arbitrarily small pressure loss) into the exact spectral-radius
bound. Only equality of these integrals with actual continuous matrix
coefficients is required; no eigenvalue or spectral-gap premise occurs. -/
theorem exp_le_spectralRadius_of_integral_growth
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (T : B →L[ℂ] B) (pairing : B →L[ℂ] ℂ) (seed : B) (P : ℝ)
    (I : ℕ → ℝ≥0∞)
    (coefficient : ∀ n, I (n + 1) = ENNReal.ofReal ‖pairing ((T ^ n) seed)‖)
    (growth : ∀ γ : ℝ, 1 < γ → ∃ N : ℕ, 0 < N ∧
      ∀ ξ : ℝ, 0 < ξ → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ v : ℝ, 0 < v ∧
        ∀ p : ℕ, 0 < p → ENNReal.ofReal (v * Real.exp ((N * p : ℕ) * (P - ξ))) ≤
          C * ENNReal.ofReal (γ ^ p) * I (N * p)) :
    ENNReal.ofReal (Real.exp P) ≤ spectralRadius ℂ T := by
  apply exp_le_spectralRadius_of_shifted_block_growth T pairing seed P
  intro δ hδ
  have halfPositive : 0 < δ / 2 := by positivity
  let γ := Real.exp (δ / 2)
  have hγ : 1 < γ := Real.one_lt_exp_iff.mpr halfPositive
  obtain ⟨N, hN, lower⟩ := growth γ hγ
  obtain ⟨C, finiteC, v, positiveV, bound⟩ := lower (δ / 2) halfPositive
  have positiveC : 0 < C.toReal + 1 := by positivity
  refine ⟨N, hN, (C.toReal + 1) / v, div_pos positiveC positiveV, ?_⟩
  intro p hp
  have positiveLength : 0 < N * p := Nat.mul_pos hN hp
  have integralIdentity : I (N * p) =
      ENNReal.ofReal ‖pairing ((T ^ (N * p - 1)) seed)‖ := by
    simpa only [Nat.sub_add_cancel positiveLength] using coefficient (N * p - 1)
  have raw := bound p hp
  rw [integralIdentity] at raw
  have rawReal : v * Real.exp ((N * p : ℕ) * (P - δ / 2)) ≤
      C.toReal * γ ^ p * ‖pairing ((T ^ (N * p - 1)) seed)‖ := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    convert raw using 1
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (Real.exp_pos _).le _)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal finiteC]
  have lengthBound : (p : ℝ) ≤ (N * p : ℕ) := by
    exact_mod_cast (show p ≤ N * p from by
      simpa only [one_mul] using Nat.mul_le_mul_right p (show 1 ≤ N from hN))
  have lossBound : Real.exp ((N * p : ℕ) * (P - δ)) * γ ^ p ≤
      Real.exp ((N * p : ℕ) * (P - δ / 2)) := by
    rw [show γ ^ p = Real.exp ((p : ℝ) * (δ / 2)) from (Real.exp_nat_mul _ _).symm,
      ← Real.exp_add, Real.exp_le_exp]
    nlinarith
  have combined : (v * Real.exp ((N * p : ℕ) * (P - δ))) * γ ^ p ≤
      ((C.toReal + 1) * ‖pairing ((T ^ (N * p - 1)) seed)‖) * γ ^ p := by
    calc
      _ ≤ v * Real.exp ((N * p : ℕ) * (P - δ / 2)) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left lossBound positiveV.le
      _ ≤ C.toReal * γ ^ p * ‖pairing ((T ^ (N * p - 1)) seed)‖ := rawReal
      _ ≤ _ := by
        have hc : C.toReal ≤ C.toReal + 1 := by linarith
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_right hc
            (mul_nonneg (pow_nonneg (Real.exp_pos (δ / 2)).le p)
              (norm_nonneg (pairing ((T ^ (N * p - 1)) seed))))
  have positiveGamma : 0 < γ ^ p := pow_pos (Real.exp_pos (δ / 2)) p
  have canceled := (mul_le_mul_iff_left₀ positiveGamma).mp combined
  have divided := (le_div_iff₀ positiveV).mpr (by simpa only [mul_comm] using canceled)
  simpa only [div_mul_eq_mul_div, mul_comm] using divided

end LeanShared.SpectralRadiusFromCoefficients
