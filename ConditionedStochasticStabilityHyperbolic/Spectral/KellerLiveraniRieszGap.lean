module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniApplication
public import AbsorbingMarkovChains.ExponentialSpectralGap

/-! # Analytic power convergence from precise KL Riesz spectral splitting

Classical complementary Riesz splitting excludes the whole leading contour
disk, including continuous spectrum. KL confinement then bounds every
complementary spectral value by the subordinate cutoff; Gelfand's formula
produces the analytic rank-one power limit. A noisy analytic power gap is not
an additional background input.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
  {d : DeterministicLeading (P 0)} {q δ : ℝ}

omit [CompleteSpace E] in
/-- Every complementary spectral value is confined below the chosen cutoff. -/
theorem ProjectorOutputs.remainder_norm_le_cutoff
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hq : 0 ≤ q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (z : ℂ) (hz : z ∈ spectrum ℂ (P ε - o.eigenvalue ε • o.projection ε)) :
    ‖z‖ ≤ q := by
  obtain hzero | ⟨hmem, hout⟩ := o.remainder_spectrum ε hε z hz
  · simpa only [hzero, norm_zero] using hq
  obtain hsmall | ⟨w, hw, hzw⟩ := o.spectral_confinement ε hε z hmem
  · exact hsmall
  obtain heq | hsub := d.spectral_separation w hw
  · rw [heq] at hzw
    exact False.elim ((not_lt_of_ge hzw) hout)
  have hnorm : ‖z‖ ≤ dist z w + ‖w‖ := by
    simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - w) w
  exact (hnorm.trans (add_le_add hzw hsub)).trans (by linarith)

/-- Genuine complementary radius is derived from the primary spectral
confinement and standard Riesz splitting. -/
theorem ProjectorOutputs.complementary_radius_lt
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (hq : 0 < q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (c : RealOperatorConjugation (P ε)) :
    spectralRadius ℂ (AbsorbingMarkovChains.CompactRankOneGap.remainder
      (P ε) (o.eigenvalue ε).re (o.vector ε) (o.mean ε)) <
      ENNReal.ofReal (o.eigenvalue ε).re := by
  have hrem : AbsorbingMarkovChains.CompactRankOneGap.remainder
      (P ε) (o.eigenvalue ε).re (o.vector ε) (o.mean ε) =
      P ε - o.eigenvalue ε • o.projection ε := by
    rw [AbsorbingMarkovChains.CompactRankOneGap.remainder, o.rank_one ε hε,
      o.eigenvalue_eq_real hδsub hδlead ε hε c]
    ext x
    simp only [Complex.ofReal_re, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [smul_comm]
  have hbound : spectralRadius ℂ (P ε - o.eigenvalue ε • o.projection ε) ≤ ENNReal.ofReal q := by
    rw [spectralRadius_eq_of_unital]
    apply iSup₂_le
    intro z hz
    rw [ENNReal.coe_nnreal_eq]
    exact ENNReal.ofReal_le_ofReal (o.remainder_norm_le_cutoff hδsub hq.le ε hε z hz)
  rw [hrem]
  exact hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
    (hq.trans (o.eigenvalue_re_gt hδlead ε hε))).2 (o.eigenvalue_re_gt hδlead ε hε))

omit [CompleteSpace E] in
/-- The analytic left eigenfunctional law follows from the Riesz projector. -/
theorem ProjectorOutputs.left_equation
    (o : ProjectorOutputs P i d q δ) (ε : ℝ≥0) (hε : ε ≤ o.window) (x : E) :
    o.mean ε (P ε x) = o.eigenvalue ε * o.mean ε x := by
  have hg : o.vector ε ≠ 0 := by
    intro hz
    have hn := o.normalization ε hε
    rw [hz, map_zero] at hn
    exact zero_ne_one hn
  have he := congrArg (fun A : E →L[ℂ] E => A x)
    ((o.projection_commutes ε hε).symm.trans (o.eigen_action ε hε))
  rw [o.rank_one ε hε] at he
  simp only [mul_apply_eq_comp, smul_apply, ContinuousLinearMap.smulRight_apply, smul_smul] at he
  have hs := (smul_left_injective ℂ hg) he
  exact hs

/-- The actual analytic normalized powers converge to the rank-one Riesz
projector, derived through Gelfand rather than postulated. -/
theorem ProjectorOutputs.tendsto_normalized_powers
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (hq : 0 < q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (c : RealOperatorConjugation (P ε)) :
    Tendsto (fun n : ℕ => (((o.eigenvalue ε).re : ℂ)⁻¹ • P ε) ^ n)
      atTop (𝓝 (o.projection ε)) := by
  let r := (o.eigenvalue ε).re
  have hr : 0 < r := hq.trans (o.eigenvalue_re_gt hδlead ε hε)
  have hright : P ε (o.vector ε) = (r : ℂ) • o.vector ε := by
    rw [o.right_equation ε hε, o.eigenvalue_eq_real hδsub hδlead ε hε c]
  have hleft : ∀ x, o.mean ε (P ε x) = (r : ℂ) * o.mean ε x := by
    intro x
    rw [o.left_equation ε hε, o.eigenvalue_eq_real hδsub hδlead ε hε c]
  obtain ⟨θ, hθ, hθ1, C, hC, hgap⟩ :=
    AbsorbingMarkovChains.CompactRankOneGap.normalized_power_gap (P ε) hr
      (o.vector ε) (o.mean ε) (o.normalization ε hε) hright hleft
      (o.complementary_radius_lt hδsub hδlead hq ε hε c)
  let C' := max C ‖(1 : E →L[ℂ] E) - o.projection ε‖
  have hall (n : ℕ) : ‖(((r : ℂ)⁻¹ • P ε) ^ n) - o.projection ε‖ ≤ C' * θ ^ n := by
    by_cases hn : n = 0
    · simpa only [hn, pow_zero, mul_one] using le_max_right C ‖(1 : E →L[ℂ] E) - o.projection ε‖
    · rw [o.rank_one ε hε]
      exact (hgap n (Nat.one_le_iff_ne_zero.mpr hn)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hθ.le n))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hall (by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1).const_mul C')

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
