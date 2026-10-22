module
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicLeadingDecay
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Horizon averages of a deterministic leading record. With `A = λ⁻¹ P`, the paired powers `ℓ(A^n
p)` tend to `m(p) ℓ(v)`, and the Birkhoff-type averages `n⁻¹ Σ_{j<n} ℓ(A^j M A^{n-j} p)` tend to
`ℓ(v) m(M v) m(p)`: every term differs from the limit by `O(ϑ^j + ϑ^{n-j})`, whose sum is
bounded uniformly in `n`. -/
public noncomputable section
open Filter Set Finset
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem DeterministicLeading.power_limit {P : E →L[ℂ] E} (d : DeterministicLeading P)
    (ℓ : E →L[ℂ] ℂ) (p : E) :
    Tendsto (fun n : ℕ => ℓ (((((d.rate : ℂ))⁻¹ • P) ^ n) p)) atTop
      (𝓝 (d.mean p * ℓ d.vector)) := by
  obtain ⟨C, ϑ, hC, hϑ0, hϑ1, decay⟩ := d.decay
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have small : Tendsto (fun n : ℕ => ‖ℓ‖ * (C * ϑ ^ n * ‖p‖)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hϑ0 hϑ1).const_mul C).mul_const ‖p‖
    simpa using this.const_mul ‖ℓ‖
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) small
  have identity : ℓ (((((d.rate : ℂ))⁻¹ • P) ^ n) p) - d.mean p * ℓ d.vector =
      ℓ (((((d.rate : ℂ))⁻¹ • P) ^ n) p - d.mean p • d.vector) := by
    rw [map_sub, map_smul, smul_eq_mul]
  rw [identity]
  exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (decay n p) (norm_nonneg _))

theorem DeterministicLeading.power_bound {P : E →L[ℂ] E} (d : DeterministicLeading P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (x : E), ‖((((d.rate : ℂ))⁻¹ • P) ^ n) x‖ ≤ K * ‖x‖ := by
  obtain ⟨C, ϑ, hC, hϑ0, hϑ1, decay⟩ := d.decay
  refine ⟨‖d.mean‖ * ‖d.vector‖ + C, by positivity, fun n x => ?_⟩
  have split : ((((d.rate : ℂ))⁻¹ • P) ^ n) x =
      (((((d.rate : ℂ))⁻¹ • P) ^ n) x - d.mean x • d.vector) + d.mean x • d.vector := by abel
  rw [split]
  calc _ ≤ ‖((((d.rate : ℂ))⁻¹ • P) ^ n) x - d.mean x • d.vector‖ + ‖d.mean x • d.vector‖ :=
        norm_add_le _ _
    _ ≤ C * ϑ ^ n * ‖x‖ + ‖d.mean‖ * ‖x‖ * ‖d.vector‖ := by
        gcongr
        · exact decay n x
        · rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (d.mean.le_opNorm x) (norm_nonneg _)
    _ ≤ C * 1 * ‖x‖ + ‖d.mean‖ * ‖x‖ * ‖d.vector‖ := by
        gcongr
        exact pow_le_one₀ hϑ0 hϑ1.le
    _ = (‖d.mean‖ * ‖d.vector‖ + C) * ‖x‖ := by ring

theorem DeterministicLeading.average_limit {P : E →L[ℂ] E} (d : DeterministicLeading P)
    (ℓ : E →L[ℂ] ℂ) (Mf : E →L[ℂ] E) (p : E) :
    Tendsto (fun n : ℕ => (∑ j ∈ range n,
        ℓ (((((d.rate : ℂ))⁻¹ • P) ^ j) (Mf (((((d.rate : ℂ))⁻¹ • P) ^ (n - j)) p)))) / n)
      atTop (𝓝 (ℓ d.vector * d.mean (Mf d.vector) * d.mean p)) := by
  obtain ⟨C, ϑ, hC, hϑ0, hϑ1, decay⟩ := d.decay
  obtain ⟨K, hK, bound⟩ := d.power_bound
  set A := (((d.rate : ℂ))⁻¹ • P) with hA
  set L0 := ℓ d.vector * d.mean (Mf d.vector) * d.mean p
  let K1 : ℝ := ‖ℓ‖ * C * (‖Mf‖ * K * ‖p‖) + ‖ℓ d.vector‖ * ‖d.mean‖ * ‖Mf‖ * C * ‖p‖
  have hK1 : 0 ≤ K1 := by positivity
  have term : ∀ n j, j ≤ n → ‖ℓ ((A ^ j) (Mf ((A ^ (n - j)) p))) - L0‖ ≤
      K1 * (ϑ ^ j + ϑ ^ (n - j)) := fun n j _ => by
    set y := Mf ((A ^ (n - j)) p)
    have hy : ‖y‖ ≤ ‖Mf‖ * K * ‖p‖ := by
      calc ‖y‖ ≤ ‖Mf‖ * ‖(A ^ (n - j)) p‖ := Mf.le_opNorm _
        _ ≤ ‖Mf‖ * (K * ‖p‖) := mul_le_mul_of_nonneg_left (bound _ _) (norm_nonneg _)
        _ = _ := by ring
    have first : ‖ℓ ((A ^ j) y) - d.mean y * ℓ d.vector‖ ≤ ‖ℓ‖ * C * (‖Mf‖ * K * ‖p‖) * ϑ ^ j := by
      have identity : ℓ ((A ^ j) y) - d.mean y * ℓ d.vector = ℓ ((A ^ j) y - d.mean y • d.vector) := by
        rw [map_sub, map_smul, smul_eq_mul]
      rw [identity]
      calc _ ≤ ‖ℓ‖ * ‖(A ^ j) y - d.mean y • d.vector‖ := ℓ.le_opNorm _
        _ ≤ ‖ℓ‖ * (C * ϑ ^ j * ‖y‖) := mul_le_mul_of_nonneg_left (decay j y) (norm_nonneg _)
        _ ≤ ‖ℓ‖ * (C * ϑ ^ j * (‖Mf‖ * K * ‖p‖)) := by gcongr
        _ = _ := by ring
    have second : ‖d.mean y * ℓ d.vector - L0‖ ≤
        ‖ℓ d.vector‖ * ‖d.mean‖ * ‖Mf‖ * C * ‖p‖ * ϑ ^ (n - j) := by
      have identity : d.mean y * ℓ d.vector - L0 =
          ℓ d.vector * d.mean (Mf ((A ^ (n - j)) p - d.mean p • d.vector)) := by
        simp only [y, L0, map_sub, map_smul, smul_eq_mul]
        ring
      rw [identity, norm_mul]
      calc _ ≤ ‖ℓ d.vector‖ * (‖d.mean‖ * (‖Mf‖ * (C * ϑ ^ (n - j) * ‖p‖))) := by
            gcongr
            calc ‖d.mean (Mf ((A ^ (n - j)) p - d.mean p • d.vector))‖ ≤
                ‖d.mean‖ * ‖Mf ((A ^ (n - j)) p - d.mean p • d.vector)‖ := d.mean.le_opNorm _
              _ ≤ ‖d.mean‖ * (‖Mf‖ * ‖(A ^ (n - j)) p - d.mean p • d.vector‖) :=
                  mul_le_mul_of_nonneg_left (Mf.le_opNorm _) (norm_nonneg _)
              _ ≤ _ := by gcongr; exact decay _ _
        _ = _ := by ring
    calc _ = ‖(ℓ ((A ^ j) y) - d.mean y * ℓ d.vector) + (d.mean y * ℓ d.vector - L0)‖ := by
          congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ ‖ℓ‖ * C * (‖Mf‖ * K * ‖p‖) * ϑ ^ j +
          ‖ℓ d.vector‖ * ‖d.mean‖ * ‖Mf‖ * C * ‖p‖ * ϑ ^ (n - j) := add_le_add first second
      _ ≤ K1 * (ϑ ^ j + ϑ ^ (n - j)) := by
        have h1 : 0 ≤ ϑ ^ j := pow_nonneg hϑ0 _
        have h2 : 0 ≤ ϑ ^ (n - j) := pow_nonneg hϑ0 _
        have h3 : 0 ≤ ‖ℓ‖ * C * (‖Mf‖ * K * ‖p‖) := by positivity
        have h4 : 0 ≤ ‖ℓ d.vector‖ * ‖d.mean‖ * ‖Mf‖ * C * ‖p‖ := by positivity
        simp only [K1]
        nlinarith [mul_nonneg h3 h2, mul_nonneg h4 h1]
  have geometric : ∀ n : ℕ, ∑ j ∈ range n, (ϑ ^ j + ϑ ^ (n - j)) ≤ 2 / (1 - ϑ) := fun n => by
    have g1 : ∑ j ∈ range n, ϑ ^ j ≤ 1 / (1 - ϑ) := by
      rw [one_div, ← tsum_geometric_of_lt_one hϑ0 hϑ1]
      exact (summable_geometric_of_lt_one hϑ0 hϑ1).sum_le_tsum _ (fun i _ => pow_nonneg hϑ0 i)
    have g2 : ∑ j ∈ range n, ϑ ^ (n - j) ≤ 1 / (1 - ϑ) := by
      have reflect : ∑ j ∈ range n, ϑ ^ (n - j) = ∑ j ∈ range n, ϑ ^ (j + 1) := by
        rw [← sum_range_reflect (fun j => ϑ ^ (j + 1)) n]
        refine sum_congr rfl fun j hj => ?_
        have : j < n := mem_range.mp hj
        congr 1
        omega
      rw [reflect]
      calc ∑ j ∈ range n, ϑ ^ (j + 1) = ϑ * ∑ j ∈ range n, ϑ ^ j := by
            rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
        _ ≤ 1 * ∑ j ∈ range n, ϑ ^ j := by
            exact mul_le_mul_of_nonneg_right hϑ1.le (sum_nonneg fun i _ => pow_nonneg hϑ0 i)
        _ ≤ 1 / (1 - ϑ) := by rw [one_mul]; exact g1
    rw [sum_add_distrib]
    have split : 2 / (1 - ϑ) = 1 / (1 - ϑ) + 1 / (1 - ϑ) := by ring
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have small : Tendsto (fun n : ℕ => K1 * (2 / (1 - ϑ)) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ small
  filter_upwards [eventually_gt_atTop 0] with n hn
  have npos : (0 : ℝ) < n := by exact_mod_cast hn
  have nC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have rewrite : (∑ j ∈ range n, ℓ ((A ^ j) (Mf ((A ^ (n - j)) p)))) / (n : ℂ) - L0 =
      (∑ j ∈ range n, (ℓ ((A ^ j) (Mf ((A ^ (n - j)) p))) - L0)) / (n : ℂ) := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    field_simp
  rw [rewrite, norm_div, Complex.norm_natCast, le_div_iff₀ npos, div_mul_cancel₀ _ npos.ne']
  calc _ ≤ ∑ j ∈ range n, ‖ℓ ((A ^ j) (Mf ((A ^ (n - j)) p))) - L0‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range n, K1 * (ϑ ^ j + ϑ ^ (n - j)) :=
        sum_le_sum fun j hj => term n j (mem_range.mp hj).le
    _ = K1 * ∑ j ∈ range n, (ϑ ^ j + ϑ ^ (n - j)) := by rw [mul_sum]
    _ ≤ K1 * (2 / (1 - ϑ)) := mul_le_mul_of_nonneg_left (geometric n) hK1

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
