module
public import LeanShared.Analysis.ExponentialSumUniqueness
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! Peripheral multiplicities from regularized trace asymptotics. Suppose a family of
scalar sequences `a j k` (regularized traces of the `k`-th powers) is, for each `j`,
asymptotically the exponential sum `∑_{γ ∈ Γ} c j γ γ^k` over finitely many unit phases,
that its peripheral coefficients converge to `d γ` along `j`, and that each `a j` stays
eventually within `δ j → 0` of one sequence `t k → 1` (normalized periodic sums).
Phased Cesàro averages then give `d γ = 1` for `γ = 1` and `d γ = 0` otherwise. -/
public noncomputable section
open Filter Finset
open scoped Topology
namespace LeanShared.PeripheralTraceRank

/-- Complex Cesàro averages of a convergent sequence converge to its limit. -/
theorem cesaro (u : ℕ → ℂ) (l : ℂ) (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * ∑ k ∈ range N, u k) atTop (𝓝 l) := by
  refine h.cesaro_smul.congr fun N => ?_
  rw [Complex.real_smul]
  push_cast
  rfl

/-- Phased averages of a unit phase. -/
theorem phase_average (γ γ0 : ℂ) (hγ : ‖γ‖ = 1) (hγ0 : ‖γ0‖ = 1) :
    Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * ∑ k ∈ range N, γ0⁻¹ ^ k * γ ^ k) atTop
      (𝓝 (if γ = γ0 then 1 else 0)) := by
  have h0 : γ0 ≠ 0 := fun h => by rw [h, norm_zero] at hγ0; exact zero_ne_one hγ0
  have rewrite (k : ℕ) : γ0⁻¹ ^ k * γ ^ k = (γ / γ0) ^ k := by
    rw [← mul_pow, inv_mul_eq_div]
  simp only [rewrite]
  by_cases equal : γ = γ0
  · subst equal
    simp only [↓reduceIte, div_self h0]
    exact LeanShared.ExponentialSumUniqueness.cesaro_one
  · simp only [equal, ↓reduceIte]
    have unit : ‖γ / γ0‖ ≤ 1 := by rw [norm_div, hγ, hγ0, div_one]
    have different : γ / γ0 ≠ 1 := fun h => equal ((div_eq_one_iff_eq h0).mp h)
    exact LeanShared.ExponentialSumUniqueness.cesaro_unit _ unit different

/-- The phased average of a sequence tending to zero tends to zero. -/
theorem phased_zero (γ0 : ℂ) (hγ0 : ‖γ0‖ = 1) (r : ℕ → ℂ) (h : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * ∑ k ∈ range N, γ0⁻¹ ^ k * r k) atTop (𝓝 0) := by
  apply cesaro
  rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢
  refine h.congr fun k => ?_
  rw [norm_mul, norm_pow, norm_inv, hγ0, inv_one, one_pow, one_mul]

/-- An eventual bound passes to Cesàro averages of nonnegative reals. -/
theorem cesaro_le (u : ℕ → ℝ) (δ : ℝ) (bound : ∀ᶠ k in atTop, u k ≤ δ) :
    ∃ v : ℕ → ℝ, Tendsto v atTop (𝓝 δ) ∧
      ∀ N : ℕ, 0 < N → ((N : ℝ))⁻¹ * ∑ k ∈ range N, u k ≤ v N := by
  let w : ℕ → ℝ := fun k => max (u k - δ) 0
  have wzero : Tendsto w atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [bound] with k hk
    exact (max_eq_right (sub_nonpos.mpr hk)).symm
  refine ⟨fun N => ((N : ℝ))⁻¹ * ∑ k ∈ range N, w k + δ, ?_, fun N hN => ?_⟩
  · simpa only [zero_add] using wzero.cesaro.add_const δ
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have pointwise : ∑ k ∈ range N, u k ≤ ∑ k ∈ range N, (w k + δ) :=
      sum_le_sum fun k _ => by
        have := le_max_left (u k - δ) 0
        linarith
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at pointwise
    calc ((N : ℝ))⁻¹ * ∑ k ∈ range N, u k ≤ ((N : ℝ))⁻¹ * (∑ k ∈ range N, w k + N * δ) :=
          mul_le_mul_of_nonneg_left pointwise (by positivity)
      _ = ((N : ℝ))⁻¹ * ∑ k ∈ range N, w k + δ := by field_simp

/-- Peripheral multiplicities from regularized trace asymptotics. -/
theorem multiplicity_eq (Γ : Finset ℂ) (unit : ∀ γ ∈ Γ, ‖γ‖ = 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (a : ι → ℕ → ℂ) (c : ι → ℂ → ℂ) (d : ℂ → ℂ) (t : ℕ → ℂ) (δ : ι → ℝ)
    (expansion : ∀ j, Tendsto (fun k => a j k - ∑ γ ∈ Γ, c j γ * γ ^ k) atTop (𝓝 0))
    (limit : ∀ γ ∈ Γ, Tendsto (fun j => c j γ) l (𝓝 (d γ)))
    (periodic : Tendsto t atTop (𝓝 1))
    (compare : ∀ j, ∀ᶠ k in atTop, ‖a j k - t k‖ ≤ δ j)
    (small : Tendsto δ l (𝓝 0)) :
    ∀ γ0 ∈ Γ, d γ0 = if γ0 = 1 then 1 else 0 := by
  intro γ0 member
  have hγ0 := unit γ0 member
  set e : ℂ := if γ0 = 1 then 1 else 0 with he
  let avg : (ℕ → ℂ) → ℕ → ℂ := fun u N => ((N : ℂ))⁻¹ * ∑ k ∈ range N, γ0⁻¹ ^ k * u k
  -- the averages of the regularized traces
  have traces (j : ι) : Tendsto (avg (a j)) atTop (𝓝 (c j γ0)) := by
    set r : ℕ → ℂ := fun k => a j k - ∑ γ ∈ Γ, c j γ * γ ^ k
    have split (N : ℕ) : avg (a j) N = avg r N +
        ∑ γ ∈ Γ, c j γ * (((N : ℂ))⁻¹ * ∑ k ∈ range N, γ0⁻¹ ^ k * γ ^ k) := by
      simp only [avg, r, mul_sub, sum_sub_distrib, Finset.mul_sum]
      rw [Finset.sum_comm (s := range N) (t := Γ)]
      have inner : ∑ y ∈ Γ, ∑ x ∈ range N, ((N : ℂ))⁻¹ * (γ0⁻¹ ^ x * (c j y * y ^ x)) =
          ∑ y ∈ Γ, ∑ x ∈ range N, c j y * (((N : ℂ))⁻¹ * (γ0⁻¹ ^ x * y ^ x)) :=
        sum_congr rfl fun y _ => sum_congr rfl fun x _ => by ring
      rw [inner]
      ring
    have phases : Tendsto (fun N : ℕ => ∑ γ ∈ Γ,
        c j γ * (((N : ℂ))⁻¹ * ∑ k ∈ range N, γ0⁻¹ ^ k * γ ^ k)) atTop
        (𝓝 (∑ γ ∈ Γ, c j γ * (if γ = γ0 then 1 else 0))) :=
      tendsto_finsetSum Γ fun γ hγ => (phase_average γ γ0 (unit γ hγ) hγ0).const_mul (c j γ)
    have collapse : ∑ γ ∈ Γ, c j γ * (if γ = γ0 then 1 else 0) = c j γ0 := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' Γ γ0 (fun γ => c j γ)]
      simp only [member, ↓reduceIte]
    rw [collapse] at phases
    have total := (phased_zero γ0 hγ0 r (expansion j)).add phases
    rw [zero_add] at total
    exact total.congr fun N => (split N).symm
  -- the averages of the periodic sums
  have periodicAverage : Tendsto (avg t) atTop (𝓝 e) := by
    have ones := phase_average 1 γ0 (by rw [norm_one]) hγ0
    have rest := phased_zero γ0 hγ0 (fun k => t k - 1) (by
      simpa only [sub_self] using periodic.sub_const 1)
    have total := rest.add ones
    rw [zero_add] at total
    have same : (if (1 : ℂ) = γ0 then (1 : ℂ) else 0) = e := by
      rw [he]
      by_cases h : γ0 = 1
      · simp only [h, ↓reduceIte]
      · simp only [h, ↓reduceIte, (Ne.symm h)]
    rw [same] at total
    refine total.congr fun N => ?_
    simp only [avg, one_pow, mul_one]
    rw [← mul_add, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun k _ => by ring
  -- each coefficient is within δ j of the target
  have close (j : ι) : ‖c j γ0 - e‖ ≤ δ j := by
    obtain ⟨v, hv, bound⟩ := cesaro_le (fun k => ‖a j k - t k‖) (δ j) (compare j)
    have lhs := ((traces j).sub periodicAverage).norm
    refine le_of_tendsto_of_tendsto lhs hv ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    refine le_trans ?_ (bound N hN)
    simp only [avg]
    rw [← mul_sub, ← sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
    rw [← mul_sub, norm_mul, norm_pow, norm_inv, hγ0, inv_one, one_pow, one_mul]
  have limitNorm : Tendsto (fun j => ‖c j γ0 - e‖) l (𝓝 ‖d γ0 - e‖) :=
    ((limit γ0 member).sub_const e).norm
  have zero : ‖d γ0 - e‖ ≤ 0 :=
    le_of_tendsto_of_tendsto limitNorm small (Eventually.of_forall close)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp zero)

end LeanShared.PeripheralTraceRank
