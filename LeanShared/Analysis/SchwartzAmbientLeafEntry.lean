module
public import LeanShared.Analysis.SchwartzAmbientBlocks

/-! Each leaf integral of a dyadic block of a supported core function is at
most `2^{-t(s) n}` times the full block norm: the L¹ norm on one leaf is at most
the leaf-family supremum of that block, which is the weighted entry divided by
the positive weight, bounded by the block-space norm. -/
public noncomputable section
open MeasureTheory Set
open scoped SchwartzMap
namespace LeanShared.SchwartzAmbientLeafEntry
open SchwartzAmbientBlocks SchwartzJetSpace

variable {E U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (D : Set E) (σ : ℕ × S → 𝓢(E, ℂ)) (t : S → ℝ)
  (hbounded : SmoothCoreBounded μ hJ leaves D σ t)

theorem leaf_le_block (f : supportedCore D) (j : ℕ × S) (a : A) :
    (∫ x, ‖ConeFourierBlocks.block (σ j) f.val x‖ ∂(leaves a).measure μ) ≤
      ‖block μ hJ leaves D σ j f‖ := by
  have hae := SchwartzAmbientRealization.realization_ae μ hJ leaves
    (ConeFourierBlocks.block (σ j) f.val) a
  have hnorm : ‖(block μ hJ leaves D σ j f) a‖ =
      ∫ x, ‖ConeFourierBlocks.block (σ j) f.val x‖ ∂(leaves a).measure μ := by
    change ‖(SchwartzAmbientRealization.realization μ hJ leaves
      (ConeFourierBlocks.block (σ j) f.val)) a‖ = _
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  rw [← hnorm]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ a

theorem weight_norm (j : ℕ × S) : ‖weight t j‖ = (2 : ℝ) ^ (t j.2 * j.1) := by
  unfold weight
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]

theorem leaf_le_core (f : supportedCore D) (j : ℕ × S) (a : A) :
    (∫ x, ‖ConeFourierBlocks.block (σ j) f.val x‖ ∂(leaves a).measure μ) ≤
      ((2 : ℝ) ^ (t j.2 * j.1))⁻¹ * ‖coreMap μ hJ leaves D σ t hbounded f‖ := by
  have hw : 0 < (2 : ℝ) ^ (t j.2 * j.1) := Real.rpow_pos_of_pos (by norm_num) _
  have entry : ‖weightedBlock μ hJ leaves D σ t j f‖ ≤ ‖coreMap μ hJ leaves D σ t hbounded f‖ := by
    rw [← coreMap_apply μ hJ leaves D σ t hbounded f j]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ j
  have weighted : ‖weightedBlock μ hJ leaves D σ t j f‖ =
      (2 : ℝ) ^ (t j.2 * j.1) * ‖block μ hJ leaves D σ j f‖ := by
    change ‖(weight t j • block μ hJ leaves D σ j) f‖ = _
    rw [LinearMap.smul_apply, norm_smul, weight_norm]
  have hb : ‖block μ hJ leaves D σ j f‖ ≤
      ((2 : ℝ) ^ (t j.2 * j.1))⁻¹ * ‖coreMap μ hJ leaves D σ t hbounded f‖ := by
    rw [le_inv_mul_iff₀ hw, ← weighted]
    exact entry
  exact (leaf_le_block μ hJ leaves D σ f j a).trans hb

end LeanShared.SchwartzAmbientLeafEntry
