module

public import LeanShared.Analysis.CompactHolderPhysicalBlocks

/-! Every literal physical input block has its leaf integral controlled by
the actual anisotropic norm. The dyadic weight is removed exactly; no
separate leaf-bound hypothesis is supplied. -/

public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction ENNReal
namespace LeanShared.CompactHolderPhysicalBlocks
open ConeDyadicSymbols

variable {E U A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  {Cp Cm : Set E} (χ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
  {K : Set E} (compact : IsCompact K) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  (t : Bool → ℝ) (margin : ∀ sign, t sign ≤ b)

set_option backward.isDefEq.respectTransparency false in
theorem weighted_leaf_bound
    (f : EuclideanSmoothHolderCore.space compact.closure hb hb1)
    (j : ℕ × Bool) (a : A) :
    ENNReal.ofReal ((2 : ℝ) ^ (t j.2 * j.1)) *
      (∫⁻ x, ‖∫ y, FourierSchwartzKernel.kernel (symbols χ Φ j) (x-y) *
        EuclideanSmoothHolderCore.physical compact.closure hb hb1 f y‖ₑ
        ∂(leaves a).measure μ) ≤
      ENNReal.ofReal ‖realize μ hJ leaves χ Φ compact hb hb1 t margin f‖ := by
  have coefficient : ‖SchwartzAmbientBlocks.weight t j‖ₑ =
      ENNReal.ofReal ((2 : ℝ) ^ (t j.2 * j.1)) := by
    rw [← ofReal_norm]
    congr 1
    simp only [SchwartzAmbientBlocks.weight, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)
  have represented := GraphLeafNorm.ambient_lintegral_le_norm μ leaves
    (realize μ hJ leaves χ Φ compact hb hb1 t margin f j)
    (fun x => SchwartzAmbientBlocks.weight t j *
      (∫ y, FourierSchwartzKernel.kernel (symbols χ Φ j) (x-y) *
        EuclideanSmoothHolderCore.physical compact.closure hb hb1 f y))
    (block_ae μ hJ leaves χ Φ compact hb hb1 t margin f j) a
  simp_rw [enorm_mul, coefficient] at represented
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at represented
  exact represented.trans (ENNReal.ofReal_le_ofReal
    (lp.norm_apply_le_norm ENNReal.top_ne_zero
      (realize μ hJ leaves χ Φ compact hb hb1 t margin f) j))

set_option backward.isDefEq.respectTransparency false in
theorem leaf_bound
    (f : EuclideanSmoothHolderCore.space compact.closure hb hb1)
    (j : ℕ × Bool) (a : A) :
    (∫⁻ x, ‖∫ y, FourierSchwartzKernel.kernel (symbols χ Φ j) (x-y) *
      EuclideanSmoothHolderCore.physical compact.closure hb hb1 f y‖ₑ
      ∂(leaves a).measure μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(t j.2 * j.1))) *
        ENNReal.ofReal ‖realize μ hJ leaves χ Φ compact hb hb1 t margin f‖ := by
  have cancellation : ENNReal.ofReal ((2 : ℝ) ^ (-(t j.2 * j.1))) *
      ENNReal.ofReal ((2 : ℝ) ^ (t j.2 * j.1)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ← Real.rpow_add (by norm_num)]
    simp only [neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one]
  have bound := mul_le_mul_of_nonneg_left
    (weighted_leaf_bound μ hJ leaves χ Φ compact hb hb1 t margin f j a)
    (show 0 ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(t j.2 * j.1))) from bot_le)
  simpa only [← mul_assoc, cancellation, one_mul] using bound

end LeanShared.CompactHolderPhysicalBlocks
