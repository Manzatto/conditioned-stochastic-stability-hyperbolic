module
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Field.GeomSum

/-! Uniqueness of exponential sums: if `∑_{μ ∈ s} c(μ) μ^n = O(ρ^n)` for a finite
set `s` of complex numbers of modulus greater than `ρ ≥ 0`, then every coefficient
vanishes. Phased Cesàro averages at a coefficient of maximal modulus isolate it.
Used to identify the outer spectrum from periodic-orbit asymptotics. -/
public noncomputable section
open Filter Finset
open scoped Topology
namespace LeanShared.ExponentialSumUniqueness

/-- Cesàro averages of the powers of a unit-modulus number different from one vanish. -/
theorem cesaro_unit (w : ℂ) (hw : ‖w‖ ≤ 1) (hne : w ≠ 1) :
    Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * ∑ n ∈ range N, w ^ n) atTop (𝓝 0) := by
  have h1 : (w - 1) ≠ 0 := sub_ne_zero.mpr hne
  have bound : ∀ N : ℕ, 0 < N → ‖((N : ℂ))⁻¹ * ∑ n ∈ range N, w ^ n‖ ≤
      (2 / ‖w - 1‖) * (1 / (N : ℝ)) := by
    intro N hN
    rw [geom_sum_eq hne, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
    have num : ‖w ^ N - 1‖ ≤ 2 := by
      calc ‖w ^ N - 1‖ ≤ ‖w ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
            rw [norm_pow, norm_one]
            exact add_le_add (pow_le_one₀ (norm_nonneg _) hw) le_rfl
        _ = 2 := by norm_num
    have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr h1
    calc ((N : ℝ))⁻¹ * (‖w ^ N - 1‖ / ‖w - 1‖) ≤ ((N : ℝ))⁻¹ * (2 / ‖w - 1‖) := by
          gcongr
      _ = (2 / ‖w - 1‖) * (1 / (N : ℝ)) := by ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ((eventually_gt_atTop 0).mono bound) ?_
  simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 / ‖w - 1‖)

/-- Cesàro averages of powers of a number of modulus less than one vanish. -/
theorem cesaro_small (w : ℂ) (hw : ‖w‖ < 1) :
    Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * ∑ n ∈ range N, w ^ n) atTop (𝓝 0) :=
  cesaro_unit w hw.le (fun h => by rw [h, norm_one] at hw; exact lt_irrefl _ hw)

theorem cesaro_one :
    Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * ∑ n ∈ range N, (1 : ℂ) ^ n) atTop (𝓝 1) := by
  have h : ∀ᶠ N : ℕ in atTop, ((N : ℂ))⁻¹ * ∑ n ∈ range N, (1 : ℂ) ^ n = 1 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')
  exact tendsto_const_nhds.congr' (h.mono fun _ h => h.symm)

/-- Exponential sums that are `O(ρ^n)` with all bases of modulus above `ρ` vanish. -/
theorem coefficients_zero (s : Finset ℂ) (c : ℂ → ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (big : ∀ μ ∈ s, ρ < ‖μ‖) (C : ℝ)
    (bound : ∀ n : ℕ, ‖∑ μ ∈ s, c μ * μ ^ n‖ ≤ C * ρ ^ n) : ∀ μ ∈ s, c μ = 0 := by
  classical
  by_contra contra
  push Not at contra
  set t := s.filter (fun μ => c μ ≠ 0) with ht
  have tne : t.Nonempty := by
    obtain ⟨μ, hμ, hc⟩ := contra
    exact ⟨μ, by rw [ht, Finset.mem_filter]; exact ⟨hμ, hc⟩⟩
  obtain ⟨k, hk, hkmax⟩ := t.exists_max_image (fun μ => ‖μ‖) tne
  have hks : k ∈ s := (Finset.mem_filter.mp hk).1
  have hck : c k ≠ 0 := (Finset.mem_filter.mp hk).2
  have hkρ : ρ < ‖k‖ := big k hks
  have hk0 : k ≠ 0 := fun h => by rw [h, norm_zero] at hkρ; linarith
  have hkn : 0 < ‖k‖ := norm_pos_iff.mpr hk0
  -- the sum over `s` is the sum over `t`
  have restrict (n : ℕ) : ∑ μ ∈ s, c μ * μ ^ n = ∑ μ ∈ t, c μ * μ ^ n := by
    rw [ht, Finset.sum_filter]
    exact Finset.sum_congr rfl fun μ _ => by split_ifs with h <;> simp_all
  -- phased averages
  set A : ℕ → ℂ := fun N => ((N : ℂ))⁻¹ * ∑ n ∈ range N, k⁻¹ ^ n * ∑ μ ∈ t, c μ * μ ^ n
  have expand (N : ℕ) : A N = ∑ μ ∈ t, c μ * (((N : ℂ))⁻¹ * ∑ n ∈ range N, (μ / k) ^ n) := by
    simp only [A, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [div_pow, div_eq_mul_inv, inv_pow]
    ring
  have limit : Tendsto A atTop (𝓝 (c k)) := by
    have each : ∀ μ ∈ t, Tendsto (fun N : ℕ => c μ * (((N : ℂ))⁻¹ * ∑ n ∈ range N, (μ / k) ^ n))
        atTop (𝓝 (if μ = k then c k else 0)) := by
      intro μ hμ
      by_cases hμk : μ = k
      · subst hμk
        simp only [↓reduceIte]
        rw [div_self hk0]
        simpa using cesaro_one.const_mul (c μ)
      · simp only [hμk, ↓reduceIte]
        have hratio : ‖μ / k‖ ≤ 1 := by
          rw [norm_div, div_le_one hkn]
          exact hkmax μ hμ
        have hne : μ / k ≠ 1 := fun h => hμk ((div_eq_one_iff_eq hk0).mp h)
        simpa using (cesaro_unit (μ / k) hratio hne).const_mul (c μ)
    have total := tendsto_finsetSum t each
    rw [Finset.sum_ite_eq' t k (fun _ => c k)] at total
    simp only [hk, ↓reduceIte] at total
    exact total.congr fun N => (expand N).symm
  have small : Tendsto A atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have q0 : 0 ≤ ρ / ‖k‖ := div_nonneg hρ hkn.le
    have q1 : ρ / ‖k‖ < 1 := (div_lt_one hkn).mpr hkρ
    have hb : ∀ N : ℕ, 0 < N → ‖A N‖ ≤ (C * (1 - ρ / ‖k‖)⁻¹) * (1 / (N : ℝ)) := by
      intro N hN
      have hC : 0 ≤ C := by
        have h := bound 0
        simp only [pow_zero, mul_one] at h
        exact (norm_nonneg _).trans h
      simp only [A, norm_mul, norm_inv, Complex.norm_natCast]
      have inner : ‖∑ n ∈ range N, k⁻¹ ^ n * ∑ μ ∈ t, c μ * μ ^ n‖ ≤ C * (1 - ρ / ‖k‖)⁻¹ := by
        calc ‖∑ n ∈ range N, k⁻¹ ^ n * ∑ μ ∈ t, c μ * μ ^ n‖
            ≤ ∑ n ∈ range N, ‖k⁻¹ ^ n * ∑ μ ∈ t, c μ * μ ^ n‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ range N, C * (ρ / ‖k‖) ^ n := by
              refine Finset.sum_le_sum fun n _ => ?_
              rw [norm_mul, norm_pow, norm_inv, ← restrict n]
              calc (‖k‖⁻¹) ^ n * ‖∑ μ ∈ s, c μ * μ ^ n‖ ≤ (‖k‖⁻¹) ^ n * (C * ρ ^ n) :=
                    mul_le_mul_of_nonneg_left (bound n) (by positivity)
                _ = C * (ρ / ‖k‖) ^ n := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring
          _ = C * ∑ n ∈ range N, (ρ / ‖k‖) ^ n := by rw [Finset.mul_sum]
          _ ≤ C * (1 - ρ / ‖k‖)⁻¹ := by
              apply mul_le_mul_of_nonneg_left _ hC
              have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) q0 q1
              rwa [← Finset.range_eq_Ico, pow_zero, one_div] at h
      calc ((N : ℝ))⁻¹ * ‖∑ n ∈ range N, k⁻¹ ^ n * ∑ μ ∈ t, c μ * μ ^ n‖
          ≤ ((N : ℝ))⁻¹ * (C * (1 - ρ / ‖k‖)⁻¹) :=
            mul_le_mul_of_nonneg_left inner (by positivity)
        _ = (C * (1 - ρ / ‖k‖)⁻¹) * (1 / (N : ℝ)) := by ring
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_gt_atTop 0).mono hb) ?_
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C * (1 - ρ / ‖k‖)⁻¹)
  exact hck (tendsto_nhds_unique limit small)

end LeanShared.ExponentialSumUniqueness
