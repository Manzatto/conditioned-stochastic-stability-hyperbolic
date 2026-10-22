module

public import ConditionedStochasticStabilityHyperbolic.Spectral.Eigenmeasure
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Leading simplicity from the actual power gap

The rank-one data used by the process construction imply uniqueness of both
leading eigenvectors and continuous left eigenfunctionals. These are derived
conclusions, rather than additional simplicity assumptions in the local and
global theorem interfaces.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology ENNReal NNReal

namespace ConditionedStochasticStabilityHyperbolic.RankOneSpectralData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : E →L[ℝ] E} {one : E} (d : RankOneSpectralData P one)

theorem eigenvector_ne_zero : d.eigenvector ≠ 0 := by
  intro hz
  have h := d.mean_eigenvector
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- A leading right eigenvector is its leading coefficient times the
constructed vector. No positivity condition on the competing vector is used. -/
theorem leading_eigenvector_eq (v : E) (hv : P v = d.rate • v) :
    v = d.mean v • d.eigenvector := by
  have hfix : d.normalizedOperator v = v := by
    simp only [normalizedOperator, smul_apply, hv, smul_smul,
      inv_mul_cancel₀ d.rate_pos.ne', one_smul]
  have hp (n : ℕ) : (d.normalizedOperator ^ n) v = v := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, hfix]
  have ht := ((ContinuousLinearMap.apply ℝ E v).continuous.continuousAt.tendsto).comp
    d.tendsto_powers
  have hc : Tendsto (fun _ : ℕ => v) atTop (𝓝 v) := tendsto_const_nhds
  have he : Tendsto (fun _ : ℕ => v) atTop (𝓝 (d.mean v • d.eigenvector)) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, hp, projection,
      ContinuousLinearMap.smulRight_apply] using ht
  exact tendsto_nhds_unique hc he

/-- The left eigenspace is likewise one-dimensional, without an independent
left simplicity hypothesis. -/
theorem leading_eigenfunctional_eq (ℓ : E →L[ℝ] ℝ)
    (hℓ : ∀ v, ℓ (P v) = d.rate * ℓ v) :
    ℓ = ℓ d.eigenvector • d.mean := by
  have hfix (v : E) : ℓ (d.normalizedOperator v) = ℓ v := by
    simp only [normalizedOperator, smul_apply, map_smul, smul_eq_mul, hℓ,
      ← mul_assoc, inv_mul_cancel₀ d.rate_pos.ne', one_mul]
  have hp (n : ℕ) (v : E) : ℓ ((d.normalizedOperator ^ n) v) = ℓ v := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_apply_eq_comp, hfix, ih]
  ext v
  have ht := (ℓ.continuous.continuousAt.tendsto.comp
    (ContinuousLinearMap.apply ℝ E v).continuous.continuousAt.tendsto).comp d.tendsto_powers
  have he : Tendsto (fun _ : ℕ => ℓ v) atTop
      (𝓝 (d.mean v * ℓ d.eigenvector)) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, hp, projection,
      ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul] using ht
  simpa only [smul_apply, smul_eq_mul, mul_comm] using
    (tendsto_nhds_unique (tendsto_const_nhds (x := ℓ v)) he)

/-- The gap gives a uniform bound on normalized powers. -/
theorem normalized_power_norm_le (n : ℕ) :
    ‖d.normalizedOperator ^ n‖ ≤ ‖d.projection‖ + d.errorConstant := by
  calc
    ‖d.normalizedOperator ^ n‖ ≤ ‖d.normalizedOperator ^ n - d.projection‖ + ‖d.projection‖ := by
      simpa only [sub_add_cancel] using norm_add_le (d.normalizedOperator ^ n - d.projection) d.projection
    _ ≤ d.errorConstant * d.decay ^ n + ‖d.projection‖ := add_le_add (d.power_gap n) le_rfl
    _ ≤ ‖d.projection‖ + d.errorConstant := by
      have h := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (n := n) d.decay_nonneg d.decay_lt_one.le) d.errorConstant_nonneg
      linarith

variable [CompleteSpace E]

/-- Every real spectral value is bounded by the leading rate. This uses the
power gap, rather than irreducibility or an additional radius hypothesis. -/
theorem real_spectrum_abs_le_rate {a : ℝ} (ha : a ∈ spectrum ℝ P) : |a| ≤ d.rate := by
  by_contra hle
  have ha_gt : d.rate < |a| := lt_of_not_ge hle
  have hratio : 1 < |a| / d.rate := (one_lt_div d.rate_pos).mpr ha_gt
  have hraw : P = d.rate • d.normalizedOperator := by
    simp only [normalizedOperator, smul_smul, mul_inv_cancel₀ d.rate_pos.ne', one_smul]
  have hbound (n : ℕ) : (|a| / d.rate) ^ n ≤
      (‖d.projection‖ + d.errorConstant) * ‖(1 : E →L[ℝ] E)‖ := by
    have hn := spectrum.norm_le_norm_mul_of_mem (spectrum.pow_mem_pow P n ha)
    rw [norm_pow, Real.norm_eq_abs] at hn
    have hnorm : ‖P ^ n‖ ≤ d.rate ^ n * (‖d.projection‖ + d.errorConstant) := by
      conv_lhs => rw [hraw, smul_pow, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg d.rate_pos.le n)]
      exact mul_le_mul_of_nonneg_left (d.normalized_power_norm_le n) (pow_nonneg d.rate_pos.le n)
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos d.rate_pos n)).mpr
    calc
      |a| ^ n ≤ ‖P ^ n‖ * ‖(1 : E →L[ℝ] E)‖ := hn
      _ ≤ (d.rate ^ n * (‖d.projection‖ + d.errorConstant)) * ‖(1 : E →L[ℝ] E)‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = _ := by ring
  obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hratio).eventually
    (eventually_gt_atTop ((‖d.projection‖ + d.errorConstant) * ‖(1 : E →L[ℝ] E)‖)) |>.exists
  exact (not_lt_of_ge (hbound n)) hn

/-- The leading rate in the process data is the actual real spectral radius. -/
theorem spectralRadius_eq_rate : spectralRadius ℝ P = ENNReal.ofReal d.rate := by
  have hhas : Module.End.HasEigenvector (P : Module.End ℝ E) d.rate d.eigenvector :=
    ⟨Module.End.mem_eigenspace_iff.mpr d.right_eigenvector, d.eigenvector_ne_zero⟩
  have hmem : d.rate ∈ spectrum ℝ P := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector hhas).mem_spectrum
  rw [spectralRadius_eq_of_unital]
  apply le_antisymm
  · apply iSup₂_le
    intro a ha
    rw [ENNReal.coe_nnreal_eq]
    exact ENNReal.ofReal_le_ofReal (d.real_spectrum_abs_le_rate ha)
  · have hb : (↑‖d.rate‖₊ : ℝ≥0∞) ≤
        ⨆ a ∈ spectrum ℝ P, (↑‖a‖₊ : ℝ≥0∞) :=
      le_iSup_of_le d.rate (le_iSup_of_le hmem le_rfl)
    simpa only [ENNReal.coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs, abs_of_pos d.rate_pos] using hb

end ConditionedStochasticStabilityHyperbolic.RankOneSpectralData
