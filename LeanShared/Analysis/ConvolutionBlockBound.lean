module
public import LeanShared.Analysis.ConeMultiplierBound

/-! Convolution contracts the block core norm. For a translation-closed leaf family,
the dyadic Fourier blocks commute with convolution by an integrable function `ρ`, and
the leaf Young inequality gives `‖ρ * f‖ ≤ ‖ρ‖₁ ‖f‖` for the block core norms, on any
pair of supports. -/
public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped SchwartzMap ENNReal Topology
namespace LeanShared.ConvolutionBlockBound
open FourierSchwartzKernel SchwartzJetSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A Fourier block of a convolution is the convolution of the block. -/
theorem block_convolution (σ : 𝓢(E, ℂ)) (ρ : E → ℂ) (hρ : Integrable ρ) (f g : 𝓢(E, ℂ))
    (hg : ∀ x, g x = ∫ y, ρ y * f (x - y)) (x : E) :
    ConeFourierBlocks.block σ g x = ∫ z, ρ z * ConeFourierBlocks.block σ f (x - z) := by
  obtain ⟨C, hC⟩ := LeafCommutator.exists_bound f
  have product : Integrable (fun p : E × E => kernel σ (x - p.1) * (ρ p.2 * f (p.1 - p.2)))
      (volume.prod volume) := by
    have base : Integrable (fun p : E × E => ‖kernel σ (x - p.1)‖ * (‖ρ p.2‖ * C))
        (volume.prod volume) :=
      ((kernel σ).integrable.comp_sub_left x).norm.mul_prod (hρ.norm.mul_const C)
    refine base.mono' ?_ (ae_of_all _ fun p => ?_)
    · exact ((kernel σ).continuous.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable.mul
        ((hρ.aestronglyMeasurable.comp_snd).mul
          (f.continuous.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)
    · rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
        (norm_nonneg _)
  rw [ConeFourierBlocks.block_apply]
  simp_rw [hg, ← integral_const_mul]
  rw [integral_integral_swap product]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rw [ConeFourierBlocks.block_apply, ← integral_const_mul]
  have shift := integral_sub_right_eq_self (μ := volume)
    (fun y => ρ z * (kernel σ (x - z - y) * f y)) z
  rw [← shift]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [show x - z - (y - z) = x - y by abel]
  ring

section Main
variable {U A S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (σ : ℕ × S → 𝓢(E, ℂ)) (t : S → ℝ)

/-- Convolution by an integrable function contracts the block core norm. -/
theorem convolution_bound [∀ c, SFinite ((leaves c).measure μ)]
    (translate : ∀ c (z : E), ∃ c', ((leaves c).measure μ).map (fun x => x + z) =
      (leaves c').measure μ)
    {D D' : Set E} (bD : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D σ t)
    (bD' : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D' σ t)
    (ρ : E → ℂ) (hρ : Integrable ρ) (ρcont : Continuous ρ) (f : supportedCore D)
    (g : supportedCore D') (hg : ∀ x, g.val x = ∫ y, ρ y * f.val (x - y)) :
    ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D' σ t bD' g‖ ≤
      (∫ y, ‖ρ y‖) * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D σ t bD f‖ := by
  set A0 := ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D σ t bD f‖ with hA0
  set R := ∫ y, ‖ρ y‖ with hR
  have A0nn : 0 ≤ A0 := norm_nonneg _
  have Rnn : 0 ≤ R := integral_nonneg fun _ => norm_nonneg _
  rw [SchwartzAmbientBlocks.coreMap_norm]
  refine Real.iSup_le (fun j => ?_) (mul_nonneg Rnn A0nn)
  obtain ⟨n, s⟩ := j
  have pow_pos' : (0 : ℝ) < (2 : ℝ) ^ (t s * n) := Real.rpow_pos_of_pos (by norm_num) _
  let family : A → Measure E := fun c => (leaves c).measure μ
  have leaf (c : A) : (∫ x, ‖ConeFourierBlocks.block (σ (n, s)) g.val x‖ ∂family c) ≤
      ((2 : ℝ) ^ (t s * n))⁻¹ * (R * A0) := by
    have pointwise (x : E) : ‖ConeFourierBlocks.block (σ (n, s)) g.val x‖ₑ ≤
        ∫⁻ z, ‖ρ z‖ₑ * ‖ConeFourierBlocks.block (σ (n, s)) f.val (x - z)‖ₑ := by
      rw [block_convolution (σ (n, s)) ρ hρ f.val g.val hg x]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      exact lintegral_congr fun z => enorm_mul _ _
    have leafSupBound : (⨆ a, ∫⁻ x, ‖ConeFourierBlocks.block (σ (n, s)) f.val x‖ₑ ∂family a) ≤
        ENNReal.ofReal (((2 : ℝ) ^ (t s * n))⁻¹ * A0) := by
      refine iSup_le fun a => ?_
      rw [← ofReal_integral_norm_eq_lintegral_enorm
        (SchwartzAmbientRealization.integrable μ leaves _ a)]
      exact ENNReal.ofReal_le_ofReal
        (SchwartzAmbientLeafEntry.leaf_le_core μ hJ leaves D σ t bD f (n, s) a)
    have total : (∫⁻ x, ‖ConeFourierBlocks.block (σ (n, s)) g.val x‖ₑ ∂family c) ≤
        ENNReal.ofReal (((2 : ℝ) ^ (t s * n))⁻¹ * (R * A0)) := by
      calc (∫⁻ x, ‖ConeFourierBlocks.block (σ (n, s)) g.val x‖ₑ ∂family c)
          ≤ ∫⁻ x, (∫⁻ z, ‖ρ z‖ₑ * ‖ConeFourierBlocks.block (σ (n, s)) f.val (x - z)‖ₑ)
              ∂family c := lintegral_mono pointwise
        _ ≤ (∫⁻ z, ‖ρ z‖ₑ) *
              ⨆ a, ∫⁻ x, ‖ConeFourierBlocks.block (σ (n, s)) f.val x‖ₑ ∂family a :=
            LeafCommutator.young (family c) family (translate c) (fun z => ‖ρ z‖ₑ)
              (fun x => ‖ConeFourierBlocks.block (σ (n, s)) f.val x‖ₑ)
              ρcont.measurable.enorm
              (ConeFourierBlocks.block (σ (n, s)) f.val).continuous.measurable.enorm
        _ ≤ ENNReal.ofReal R * ENNReal.ofReal (((2 : ℝ) ^ (t s * n))⁻¹ * A0) := by
            rw [hR, ofReal_integral_norm_eq_lintegral_enorm hρ]
            exact mul_le_mul_right leafSupBound _
        _ = ENNReal.ofReal (((2 : ℝ) ^ (t s * n))⁻¹ * (R * A0)) := by
            rw [← ENNReal.ofReal_mul Rnn]
            congr 1
            ring
    rw [← ofReal_integral_norm_eq_lintegral_enorm
      (SchwartzAmbientRealization.integrable μ leaves _ c)] at total
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.mpr pow_pos'.le)
      (mul_nonneg Rnn A0nn))).mp total
  have blockNorm : ‖SchwartzAmbientBlocks.block μ hJ leaves D' σ (n, s) g‖ ≤
      ((2 : ℝ) ^ (t s * n))⁻¹ * (R * A0) := by
    refine lp.norm_le_of_forall_le (mul_nonneg (inv_nonneg.mpr pow_pos'.le)
      (mul_nonneg Rnn A0nn)) fun c => ?_
    rw [ConeMultiplierBound.block_component_norm]
    exact leaf c
  have weighted : ‖SchwartzAmbientBlocks.weightedBlock μ hJ leaves D' σ t (n, s) g‖ =
      (2 : ℝ) ^ (t s * n) * ‖SchwartzAmbientBlocks.block μ hJ leaves D' σ (n, s) g‖ := by
    change ‖(SchwartzAmbientBlocks.weight t (n, s) •
      SchwartzAmbientBlocks.block μ hJ leaves D' σ (n, s)) g‖ = _
    rw [LinearMap.smul_apply, norm_smul, SchwartzAmbientLeafEntry.weight_norm]
  rw [weighted]
  calc (2 : ℝ) ^ (t s * n) * ‖SchwartzAmbientBlocks.block μ hJ leaves D' σ (n, s) g‖
      ≤ (2 : ℝ) ^ (t s * n) * (((2 : ℝ) ^ (t s * n))⁻¹ * (R * A0)) :=
        mul_le_mul_of_nonneg_left blockNorm pow_pos'.le
    _ = R * A0 := by rw [← mul_assoc, mul_inv_cancel₀ pow_pos'.ne', one_mul]

end Main
end LeanShared.ConvolutionBlockBound
