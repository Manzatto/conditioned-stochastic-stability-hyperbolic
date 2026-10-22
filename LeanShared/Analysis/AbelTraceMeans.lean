module
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Complex.Basic

/-! Abel means along a ray towards a unit complex number. With `w = γ s`, `s > 1`, the
weights `(w - γ) w⁻¹ w⁻ᵏ` have total mass one; Abel means of a sequence eventually
bounded by `D` are at most `D + η` for `s` close to one, and the Abel means of the
constant sequence tend to `1` if `γ = 1` and to `0` otherwise. -/
public noncomputable section
open Filter Finset
open scoped Topology
namespace LeanShared.AbelTraceMeans

/-- The Abel weight at time `k` along the ray `w = γ s`. -/
@[expose] def coef (γ : ℂ) (s : ℝ) (k : ℕ) : ℂ :=
  (γ * s - γ) * (γ * s)⁻¹ * ((γ * s)⁻¹) ^ k

theorem norm_coef (γ : ℂ) (unit : ‖γ‖ = 1) (s : ℝ) (hs : 1 < s) (k : ℕ) :
    ‖coef γ s k‖ = (s - 1) * (s⁻¹) ^ (k + 1) := by
  have s0 : 0 < s := by linarith
  have normS : ‖(γ * s : ℂ)‖ = s := by
    rw [norm_mul, unit, one_mul, Complex.norm_real, Real.norm_of_nonneg s0.le]
  have normSub : ‖(γ * s - γ : ℂ)‖ = s - 1 := by
    rw [show (γ * s - γ : ℂ) = γ * ((s - 1 : ℝ) : ℂ) by push_cast; ring, norm_mul, unit,
      one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [coef, norm_mul, norm_mul, norm_pow, norm_inv, normS, normSub, pow_succ]
  ring

theorem hasSum_norm (s : ℝ) (hs : 1 < s) :
    HasSum (fun k : ℕ => (s - 1) * (s⁻¹) ^ (k + 1)) 1 := by
  have s0 : 0 < s := by linarith
  have small : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
  have geom := (hasSum_geometric_of_lt_one (inv_nonneg.mpr s0.le) small).mul_left
    ((s - 1) * s⁻¹)
  have h1 : s - 1 ≠ 0 := (sub_pos.mpr hs).ne'
  convert geom using 1
  · funext k; rw [pow_succ]; ring
  · field_simp

theorem summable_bound (γ : ℂ) (unit : ‖γ‖ = 1) (s : ℝ) (hs : 1 < s) (u : ℕ → ℂ) (U : ℝ)
    (bound : ∀ k, ‖u k‖ ≤ U) : Summable (fun k => coef γ s k * u k) := by
  refine Summable.of_norm_bounded ((hasSum_norm s hs).summable.mul_right U) fun k => ?_
  rw [norm_mul, norm_coef γ unit s hs]
  have positive := pow_pos (inv_pos.mpr (show (0 : ℝ) < s by linarith)) (k + 1)
  have weight : 0 ≤ (s - 1) * (s⁻¹) ^ (k + 1) := by nlinarith
  exact mul_le_mul_of_nonneg_left (bound k) weight

/-- Abel means of eventually `D`-bounded sequences. -/
theorem abel_bound (γ : ℂ) (unit : ‖γ‖ = 1) (u : ℕ → ℂ) (D : ℝ)
    (eventually : ∀ᶠ k in atTop, ‖u k‖ ≤ D) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ s in 𝓝[>] (1 : ℝ), Summable (fun k => coef γ s k * u k) ∧
      ‖∑' k, coef γ s k * u k‖ ≤ D + η := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp eventually
  have D0 : 0 ≤ D := (norm_nonneg _).trans (hK K le_rfl)
  set U := ∑ k ∈ range K, ‖u k‖ with hU
  have U0 : 0 ≤ U := sum_nonneg fun k _ => norm_nonneg _
  have global (k : ℕ) : ‖u k‖ ≤ U + D := by
    by_cases hk : k < K
    · have := single_le_sum (f := fun k => ‖u k‖) (fun k _ => norm_nonneg _)
        (mem_range.mpr hk)
      linarith
    · linarith [hK k (not_lt.mp hk)]
  have near : ∀ᶠ s in 𝓝[>] (1 : ℝ), s - 1 < η / (U + 1) := by
    have lim : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝 0) := by
      have h : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) := tendsto_id.sub_const 1
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact lim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [near, self_mem_nhdsWithin] with s close hs
  change 1 < s at hs
  have s0 : 0 < s := by linarith
  have summable := summable_bound γ unit s hs u (U + D) global
  refine ⟨summable, ?_⟩
  have weights (k : ℕ) : (s - 1) * (s⁻¹) ^ (k + 1) ≤ s - 1 := by
    have : (s⁻¹) ^ (k + 1) ≤ 1 := pow_le_one₀ (inv_nonneg.mpr s0.le) (inv_le_one_of_one_le₀ hs.le)
    nlinarith
  rw [← summable.sum_add_tsum_nat_add K]
  have head : ‖∑ k ∈ range K, coef γ s k * u k‖ ≤ (s - 1) * U := by
    refine (norm_sum_le _ _).trans ?_
    rw [hU, mul_sum]
    refine sum_le_sum fun k _ => ?_
    rw [norm_mul, norm_coef γ unit s hs]
    exact mul_le_mul_of_nonneg_right (weights k) (norm_nonneg _)
  have tailSummable : Summable (fun k => ‖coef γ s (k + K) * u (k + K)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      (((hasSum_norm s hs).summable.comp_injective (add_left_injective K)).mul_right (U + D))
    rw [norm_mul, norm_coef γ unit s hs]
    have positive := pow_pos (inv_pos.mpr s0) (k + K + 1)
    have weight : 0 ≤ (s - 1) * (s⁻¹) ^ (k + K + 1) := by nlinarith
    exact mul_le_mul_of_nonneg_left (global _) weight
  have tail : ‖∑' k, coef γ s (k + K) * u (k + K)‖ ≤ D := by
    refine (norm_tsum_le_tsum_norm tailSummable).trans ?_
    have comparison : ∀ k, ‖coef γ s (k + K) * u (k + K)‖ ≤ (s - 1) * (s⁻¹) ^ (k + 1) * D := by
      intro k
      rw [norm_mul, norm_coef γ unit s hs]
      have decay : (s⁻¹) ^ (k + K + 1) ≤ (s⁻¹) ^ (k + 1) :=
        pow_le_pow_of_le_one (inv_nonneg.mpr s0.le) (inv_le_one_of_one_le₀ hs.le) (by omega)
      have := hK (k + K) (by omega)
      have nonneg : 0 ≤ (s - 1) * (s⁻¹) ^ (k + K + 1) := by
        have := pow_pos (inv_pos.mpr s0) (k + K + 1); nlinarith
      calc (s - 1) * (s⁻¹) ^ (k + K + 1) * ‖u (k + K)‖
          ≤ (s - 1) * (s⁻¹) ^ (k + K + 1) * D := mul_le_mul_of_nonneg_left this nonneg
        _ ≤ (s - 1) * (s⁻¹) ^ (k + 1) * D :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left decay (by linarith)) D0
    calc ∑' k, ‖coef γ s (k + K) * u (k + K)‖ ≤ ∑' k, (s - 1) * (s⁻¹) ^ (k + 1) * D :=
          Summable.tsum_le_tsum comparison tailSummable ((hasSum_norm s hs).summable.mul_right D)
      _ = D := by rw [tsum_mul_right, (hasSum_norm s hs).tsum_eq, one_mul]
  have product : (s - 1) * U ≤ η := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < U + 1)).mp close
    nlinarith
  calc ‖∑ k ∈ range K, coef γ s k * u k + ∑' k, coef γ s (k + K) * u (k + K)‖
      ≤ ‖∑ k ∈ range K, coef γ s k * u k‖ + ‖∑' k, coef γ s (k + K) * u (k + K)‖ :=
        norm_add_le _ _
    _ ≤ D + η := by linarith

/-- Abel means of the constant sequence. -/
theorem hasSum_coef (γ : ℂ) (unit : ‖γ‖ = 1) (s : ℝ) (hs : 1 < s) :
    HasSum (coef γ s) ((γ * s - γ) / (γ * s - 1)) := by
  have normS : ‖(γ * s : ℂ)‖ = s := by
    rw [norm_mul, unit, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have small : ‖(γ * s : ℂ)⁻¹‖ < 1 := by rw [norm_inv, normS]; exact inv_lt_one_of_one_lt₀ hs
  have ne : (γ * s : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at normS; linarith
  have ne1 : (γ * s - 1 : ℂ) ≠ 0 := by
    intro h
    have : (γ * s : ℂ) = 1 := sub_eq_zero.mp h
    rw [this, norm_one] at normS; linarith
  have ne2 : (1 - (γ * s : ℂ)⁻¹) ≠ 0 := by
    intro h
    have : (γ * s : ℂ)⁻¹ = 1 := (sub_eq_zero.mp h).symm
    rw [this, norm_one] at small; exact lt_irrefl _ small
  have geom := (hasSum_geometric_of_norm_lt_one small).mul_left ((γ * s - γ) * (γ * s)⁻¹)
  convert geom using 1
  · funext k; rfl
  · field_simp
    have denom : (γ * s : ℂ) * (1 - 1 / (γ * s)) = γ * s - 1 := by
      rw [mul_sub, mul_one, mul_one_div_cancel ne]
    rw [denom, mul_div_assoc, div_self ne1, mul_one]

theorem constant_limit (γ : ℂ) :
    Tendsto (fun s : ℝ => (γ * s - γ) / (γ * s - 1)) (𝓝[>] 1)
      (𝓝 (if γ = 1 then 1 else 0)) := by
  by_cases one : γ = 1
  · simp only [one, ↓reduceIte, one_mul]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have : ((s : ℂ) - 1) ≠ 0 := by
      intro h
      have : (s : ℂ) = ((1 : ℝ) : ℂ) := by rw [Complex.ofReal_one]; exact sub_eq_zero.mp h
      exact (ne_of_gt (show (1 : ℝ) < s from hs)) (Complex.ofReal_injective this)
    exact (div_self this).symm
  · simp only [one, ↓reduceIte]
    have denom : (γ * ((1 : ℝ) : ℂ) - 1) ≠ 0 := by
      rw [Complex.ofReal_one, mul_one]; exact sub_ne_zero.mpr one
    have cont : ContinuousAt (fun s : ℝ => (γ * s - γ) / (γ * s - 1)) 1 :=
      ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).continuousAt.div
        ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).continuousAt denom
    have := cont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
    simpa only [Complex.ofReal_one, mul_one, sub_self, zero_div] using this

/-- Abel means of traces close to a sequence tending to one. -/
theorem abel_compare (γ : ℂ) (unit : ‖γ‖ = 1) (a t : ℕ → ℂ) (δ : ℝ)
    (compare : ∀ᶠ k in atTop, ‖a k - t k‖ ≤ δ) (periodic : Tendsto t atTop (𝓝 1))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ x, HasSum (fun k => coef γ s k * a k) x →
      ‖x - (if γ = 1 then 1 else 0)‖ ≤ δ + η := by
  have periodic' : ∀ᶠ k in atTop, ‖t k - 1‖ ≤ η / 4 := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp periodic).eventually
      (ge_mem_nhds (show (0 : ℝ) < η / 4 by positivity))
    exact this
  have constant := (tendsto_iff_norm_sub_tendsto_zero.mp (constant_limit γ)).eventually
    (ge_mem_nhds (show (0 : ℝ) < η / 4 by positivity))
  filter_upwards [abel_bound γ unit (fun k => a k - t k) δ compare (η / 4) (by positivity),
    abel_bound γ unit (fun k => t k - 1) (η / 4) periodic' (η / 4) (by positivity),
    constant, self_mem_nhdsWithin]
    with s first second third hs x hx
  change 1 < s at hs
  have split : HasSum (fun k => coef γ s k * a k)
      ((∑' k, coef γ s k * (a k - t k)) + (∑' k, coef γ s k * (t k - 1)) +
        (γ * s - γ) / (γ * s - 1)) := by
    have := (first.1.hasSum.add second.1.hasSum).add (hasSum_coef γ unit s hs)
    convert this using 1
    funext k; ring
  rw [hx.unique split]
  calc ‖(∑' k, coef γ s k * (a k - t k)) + (∑' k, coef γ s k * (t k - 1)) +
        (γ * s - γ) / (γ * s - 1) - (if γ = 1 then 1 else 0)‖
      ≤ ‖∑' k, coef γ s k * (a k - t k)‖ + ‖∑' k, coef γ s k * (t k - 1)‖ +
        ‖(γ * s - γ) / (γ * s - 1) - (if γ = 1 then 1 else 0)‖ := by
        rw [add_sub_assoc]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (δ + η / 4) + (η / 4 + η / 4) + η / 4 := add_le_add (add_le_add first.2 second.2) third
    _ = δ + η := by ring

end LeanShared.AbelTraceMeans
