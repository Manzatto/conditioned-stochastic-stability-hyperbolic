module
public import LeanShared.Analysis.LowOrderBlockPairing
public import LeanShared.Analysis.AnnularDualSupport
public import LeanShared.Analysis.LeafCommutator
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Dyadic antiderivatives. For a block `u = Q f` whose symbol
is an annular symbol dilated by `r`, the smooth compactly supported multipliers
`h_i(η) = -i ⟨b_i, η⟩ |η|^{-2} ϑ(η)` (`ϑ` the annular dual cutoff, `b` an
orthonormal basis) give Schwartz functions `G_i = r^{-1} (h_i(r^{-1} ·)) u` with
`u = ∑_i ∂_{b_i} G_i`; leafwise Young bounds each `G_i` by `r^{-1}` times the
fixed kernel mass of `h_i` times the leaf size of `u`.
-/
public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped SchwartzMap ENNReal Topology ContDiff FourierTransform
open LineDeriv
namespace LeanShared.DyadicAntiderivative
open FourierSchwartzKernel ConeFourierBlocks ConeDyadicSymbols

variable {E ι A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  (b : OrthonormalBasis ι ℝ E) (χ : RadialCutoff)

/-- The antiderivative multiplier. -/
@[expose] def multiplier (i : ι) (η : E) : ℂ :=
  -Complex.I * ((inner ℝ (b i) η / ‖η‖ ^ 2 : ℝ) : ℂ) * AnnularDualCutoff.symbol χ η

omit [MeasurableSpace E] [BorelSpace E] in
theorem multiplier_smooth (i : ι) : ContDiff ℝ ∞ (multiplier b χ i) := by
  rw [contDiff_iff_contDiffAt]
  intro η
  by_cases hη : η = 0
  · subst hη
    have zero : multiplier b χ i =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1 / 4)] with ξ hξ
      rw [Metric.mem_ball, dist_zero_right] at hξ
      simp only [multiplier, AnnularDualCutoff.collar χ hξ, mul_zero]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq zero
  · have hn : ‖η‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hη)
    have real : ContDiffAt ℝ ∞ (fun ξ : E => inner ℝ (b i) ξ / ‖ξ‖ ^ 2) η :=
      ((innerSL ℝ (b i)).contDiff.contDiffAt).div (contDiff_norm_sq ℝ).contDiffAt hn
    have complex : ContDiffAt ℝ ∞ (fun ξ : E => ((inner ℝ (b i) ξ / ‖ξ‖ ^ 2 : ℝ) : ℂ)) η :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp η real
    exact (contDiffAt_const.mul complex).mul ((AnnularDualCutoff.symbol χ).smooth ⊤).contDiffAt

omit [MeasurableSpace E] [BorelSpace E] in
theorem multiplier_compact (i : ι) : HasCompactSupport (multiplier b χ i) := by
  have h : HasCompactSupport ((fun η : E => -Complex.I * ((inner ℝ (b i) η / ‖η‖ ^ 2 : ℝ) : ℂ)) *
      (AnnularDualCutoff.symbol (E := E) χ : E → ℂ)) := (AnnularDualCutoff.compact χ).mul_left
  exact h

/-- The antiderivative symbol as a Schwartz function. -/
@[expose] def symbolAt (i : ι) : 𝓢(E, ℂ) :=
  FourierSchwartzKernel.symbol (multiplier b χ i) (multiplier_compact b χ i)
    (multiplier_smooth b χ i)

omit [MeasurableSpace E] [BorelSpace E] in
theorem symbolAt_apply (i : ι) (η : E) : symbolAt b χ i η = multiplier b χ i η :=
  FourierSchwartzKernel.symbol_apply _ _ _ η

/-- The antiderivatives of a dilated block. -/
def antiderivative (σ : 𝓢(E, ℂ)) (r : ℝ) (hr : 0 < r) (f : 𝓢(E, ℂ)) (i : ι) : 𝓢(E, ℂ) :=
  ((r⁻¹ : ℝ) : ℂ) • block (dilateSymbol (symbolAt b χ i) r hr) (block (dilateSymbol σ r hr) f)

/-- The algebraic Fourier identity behind the antiderivatives. -/
theorem fourier_identity (r : ℝ) (hr : 0 < r) (ξ : E) (X : ℂ) :
    ∑ i, (2 * Real.pi * Complex.I) * ((inner ℝ ξ (b i) : ℝ) : ℂ) *
        (((r⁻¹ : ℝ) : ℂ) * (multiplier b χ i (r⁻¹ • (2 * Real.pi) • ξ) * X)) =
      AnnularDualCutoff.symbol χ (r⁻¹ • (2 * Real.pi) • ξ) * X := by
  set η : E := r⁻¹ • (2 * Real.pi) • ξ with hη
  have hπ : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hξ : ξ = (r * (2 * Real.pi)⁻¹) • η := by
    rw [hη, smul_smul, smul_smul]
    field_simp
    simp
  by_cases zero : η = 0
  · have hξ0 : ξ = 0 := by rw [hξ, zero, smul_zero]
    simp [hξ0, zero, AnnularDualCutoff.collar χ (by simp : ‖(0 : E)‖ < 1 / 4)]
  · have hn : ‖η‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr zero)
    have inner_eq (i : ι) : inner ℝ ξ (b i) = r * (2 * Real.pi)⁻¹ * inner ℝ (b i) η := by
      rw [hξ, real_inner_smul_left, real_inner_comm]
    have term (i : ι) : (2 * Real.pi * Complex.I) * ((inner ℝ ξ (b i) : ℝ) : ℂ) *
        (((r⁻¹ : ℝ) : ℂ) * (multiplier b χ i η * X)) =
          (((inner ℝ (b i) η) ^ 2 / ‖η‖ ^ 2 : ℝ) : ℂ) * (AnnularDualCutoff.symbol χ η * X) := by
      rw [inner_eq, multiplier]
      have eI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      have ea : 2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ))⁻¹ = 1 :=
        mul_inv_cancel₀ (by exact_mod_cast hπ)
      have ec : (r : ℂ) * (r : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
      set W : ℂ := ((inner ℝ (b i) η : ℝ) : ℂ) ^ 2 * (((‖η‖ : ℝ) : ℂ) ^ 2)⁻¹ *
        AnnularDualCutoff.symbol χ η * X with hW
      push_cast
      linear_combination (-(2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ))⁻¹) * ((r : ℂ) * (r : ℂ)⁻¹) * W) * eI +
        ((r : ℂ) * (r : ℂ)⁻¹ * W) * ea + W * ec
    simp_rw [term]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.sum_div, b.sum_sq_inner_right,
      div_self hn, Complex.ofReal_one, one_mul]

/-- The antiderivatives reconstruct the block. -/
theorem sum_lineDeriv (σ : 𝓢(E, ℂ)) (annulus : ∀ ξ, σ ξ ≠ 0 → 1 / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2)
    (r : ℝ) (hr : 0 < r) (f : 𝓢(E, ℂ)) :
    ∑ i, ∂_{b i} (antiderivative b χ σ r hr f i) = block (dilateSymbol σ r hr) f := by
  have h : 𝓕 (∑ i, ∂_{b i} (antiderivative b χ σ r hr f i)) =
      𝓕 (block (dilateSymbol σ r hr) f) := by
    ext ξ
    rw [FourierTransform.fourier_sum, sum_apply]
    have each (i : ι) : 𝓕 (∂_{b i} (antiderivative b χ σ r hr f i)) ξ =
        (2 * Real.pi * Complex.I) * ((inner ℝ ξ (b i) : ℝ) : ℂ) *
          (((r⁻¹ : ℝ) : ℂ) * (multiplier b χ i (r⁻¹ • (2 * Real.pi) • ξ) *
            𝓕 (block (dilateSymbol σ r hr) f) ξ)) := by
      have temperate : (fun x : E => inner ℝ x (b i)).HasTemperateGrowth :=
        ((innerSL ℝ).flip (b i)).hasTemperateGrowth
      rw [SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
        SchwartzMap.smulLeftCLM_apply_apply temperate, antiderivative, FourierTransform.fourier_smul, smul_apply,
        fourier_block, dilateSymbol_apply, symbolAt_apply]
      simp only [smul_eq_mul, Complex.real_smul]
      ring
    simp_rw [each]
    rw [fourier_identity b χ r hr ξ]
    rw [fourier_block, dilateSymbol_apply]
    by_cases nonzero : σ (r⁻¹ • (2 * Real.pi) • ξ) = 0
    · rw [nonzero, zero_mul, mul_zero]
    · obtain ⟨lower, upper⟩ := annulus _ nonzero
      rw [AnnularDualCutoff.one χ lower upper, one_mul]
  have := congrArg (fun g : 𝓢(E, ℂ) => 𝓕⁻ g) h
  simpa only [FourierPair.fourierInv_fourier_eq] using this

theorem antiderivative_apply_sum (σ : 𝓢(E, ℂ)) (annulus : ∀ ξ, σ ξ ≠ 0 → 1 / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2)
    (r : ℝ) (hr : 0 < r) (f : 𝓢(E, ℂ)) (y : E) :
    block (dilateSymbol σ r hr) f y = ∑ i, fderiv ℝ (antiderivative b χ σ r hr f i) y (b i) := by
  rw [← sum_lineDeriv b χ σ annulus r hr f, sum_apply]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- Leafwise Young for one convolution block. -/
theorem leaf_block_le (ν : Measure E) [SFinite ν] (family : A → Measure E)
    (translate : ∀ z : E, ∃ a, ν.map (fun x => x + z) = family a) (τ u : 𝓢(E, ℂ)) :
    (∫⁻ x, ‖block τ u x‖ₑ ∂ν) ≤
      ENNReal.ofReal (∫ z, ‖kernel τ z‖) * ⨆ c, ∫⁻ x, ‖u x‖ₑ ∂family c := by
  have pointwise (x : E) : ‖block τ u x‖ₑ ≤ ∫⁻ z, ‖kernel τ z‖ₑ * ‖u (x - z)‖ₑ := by
    rw [block_apply]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_sub_left_eq_self (fun z => ‖kernel τ z‖ₑ * ‖u (x - z)‖ₑ) x]
    apply le_of_eq
    congr 1
    funext y
    rw [enorm_mul, sub_sub_cancel]
  calc (∫⁻ x, ‖block τ u x‖ₑ ∂ν) ≤ ∫⁻ x, (∫⁻ z, ‖kernel τ z‖ₑ * ‖u (x - z)‖ₑ) ∂ν :=
        lintegral_mono pointwise
    _ ≤ (∫⁻ z, ‖kernel τ z‖ₑ) * ⨆ c, ∫⁻ x, ‖u x‖ₑ ∂family c :=
        LeafCommutator.young ν family translate _ _ (kernel τ).continuous.measurable.enorm
          u.continuous.measurable.enorm
    _ = _ := by rw [← ofReal_integral_norm_eq_lintegral_enorm (kernel τ).integrable]

/-- Each antiderivative gains `r^{-1}` on every leaf. -/
theorem leaf_antiderivative_le (ν : Measure E) [SFinite ν] (family : A → Measure E)
    (translate : ∀ z : E, ∃ a, ν.map (fun x => x + z) = family a)
    (σ : 𝓢(E, ℂ)) (r : ℝ) (hr : 0 < r) (f : 𝓢(E, ℂ)) (i : ι) :
    (∫⁻ x, ‖antiderivative b χ σ r hr f i x‖ₑ ∂ν) ≤
      ENNReal.ofReal r⁻¹ * ENNReal.ofReal (∫ z, ‖kernel (symbolAt b χ i) z‖) *
        ⨆ c, ∫⁻ x, ‖block (dilateSymbol σ r hr) f x‖ₑ ∂family c := by
  have scale (x : E) : ‖antiderivative b χ σ r hr f i x‖ₑ = ENNReal.ofReal r⁻¹ *
      ‖block (dilateSymbol (symbolAt b χ i) r hr) (block (dilateSymbol σ r hr) f) x‖ₑ := by
    rw [antiderivative, smul_apply, smul_eq_mul, enorm_mul, ← ofReal_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  simp_rw [scale]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc]
  gcongr
  have h := leaf_block_le ν family translate (dilateSymbol (symbolAt b χ i) r hr)
    (block (dilateSymbol σ r hr) f)
  rwa [integral_norm_kernel_dilateSymbol] at h

end LeanShared.DyadicAntiderivative
