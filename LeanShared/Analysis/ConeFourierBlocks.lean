module

public import LeanShared.Analysis.ConeDyadicResolution
public import LeanShared.Analysis.SchwartzJetKernel
public import Mathlib.Analysis.Fourier.Convolution

/-!
# Actual cone Fourier blocks and smooth-core separation

The manuscript's physical convolution uses the constructed inverse kernels.
In Mathlib's Fourier convention its multiplier is evaluated at `2π ξ`.
This change of convention is proved explicitly. The actual partition of
unity then proves separation of smooth functions by all their blocks.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform Convolution

namespace LeanShared.ConeFourierBlocks

open FourierSchwartzKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def mathlibSymbol (σ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  dilateSymbol σ (2 * Real.pi)⁻¹ (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem mathlibSymbol_apply (σ : 𝓢(E, ℂ)) (ξ : E) :
    mathlibSymbol σ ξ = σ ((2 * Real.pi) • ξ) := by simp [mathlibSymbol]

theorem kernel_eq_fourierInv (σ : 𝓢(E, ℂ)) : kernel σ = 𝓕⁻ (mathlibSymbol σ) := by
  borelize E
  ext x
  rw [kernel_apply, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  simp only [mathlibSymbol_apply, smul_eq_mul]
  have hphase (ξ : E) : 2 * Real.pi * inner ℝ ξ x = inner ℝ x ((2 * Real.pi) • ξ) := by
    rw [real_inner_smul_right, real_inner_comm]
  have hchange := Measure.integral_comp_smul_of_nonneg volume
    (fun ξ : E => Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * σ ξ)
    (2 * Real.pi) (hR := (mul_pos (by norm_num) Real.pi_pos).le)
  rw [normalization]
  simp only [RCLike.real_smul_eq_coe_mul] at hchange
  calc
    _ = ∫ ξ : E, Complex.exp (Complex.I * (inner ℝ x ((2 * Real.pi) • ξ) : ℂ)) *
        σ ((2 * Real.pi) • ξ) := hchange.symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun ξ => by
        dsimp only
        rw [← hphase]
        congr 2
        exact mul_comm _ _

theorem fourier_kernel (σ : 𝓢(E, ℂ)) : 𝓕 (kernel σ) = mathlibSymbol σ := by
  rw [kernel_eq_fourierInv]
  simp

/-- The physical smoothing block is an actual Schwartz convolution CLM. -/
def block (σ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (kernel σ)

theorem block_apply (σ f : 𝓢(E, ℂ)) (x : E) :
    block σ f x = ∫ y : E, kernel σ (x - y) * f y := by
  rw [block, ← SchwartzMap.convolution_flip, SchwartzMap.convolution_apply,
    convolution_def]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by simp; ring

theorem fourier_block (σ f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (block σ f) ξ = σ ((2 * Real.pi) • ξ) * 𝓕 f ξ := by
  rw [block, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    fourier_kernel, mathlibSymbol_apply]
  rfl

/-- The actual bilinear test pairing of a smooth function, with no separately
supplied distribution realization. -/
def integralPairing : 𝓢(E, ℂ) →ₗ[ℂ] (𝓢(E, ℂ) →ₗ[ℂ] ℂ) where
  toFun f := ((SchwartzMap.integralCLM ℂ volume).comp
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f)).toLinearMap
  map_add' f g := by
    ext h
    change (SchwartzMap.integralCLM ℂ volume)
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (f + g) h) = _
    rw [map_add, add_apply, map_add]
    rfl
  map_smul' c f := by
    ext h
    change (SchwartzMap.integralCLM ℂ volume)
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (c • f) h) = _
    rw [map_smul, smul_apply, map_smul]
    rfl

@[simp] theorem integralPairing_apply (f h : 𝓢(E, ℂ)) :
    integralPairing f h = ∫ y : E, f y * h y := rfl

/-- On the supported smooth core, the actual cutoff test pairing is exactly
the physical convolution block. The cutoff may have larger support. -/
theorem integralPairing_cutoffKernel (σ f χ : 𝓢(E, ℂ)) {S : Set E}
    (hf : ∀ y ∉ S, f y = 0) (hχ : ∀ y ∈ S, χ y = 1) (x : E) :
    integralPairing f (SchwartzJetKernel.cutoffKernel χ (kernel σ) x) = block σ f x := by
  rw [integralPairing_apply, block_apply]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    change f y * SchwartzJetKernel.cutoffKernel χ (kernel σ) x y = kernel σ (x - y) * f y
    rw [SchwartzJetKernel.cutoffKernel_apply]
    by_cases hy : y ∈ S
    · rw [hχ y hy, one_mul, mul_comm]
    · rw [hf y hy, zero_mul, mul_zero]

variable {Cplus Cminus : Set E} (χ : ConeDyadicSymbols.RadialCutoff)
  (Φ : ConeDyadicSymbols.AngularCutoff Cplus Cminus)

/-- The actual cone blocks separate the smooth core, by the proved partition. -/
theorem eq_zero_of_blocks_zero (f : 𝓢(E, ℂ))
    (hf : ∀ j : ℕ × Bool, block (ConeDyadicSymbols.symbols χ Φ j) f = 0) : f = 0 := by
  have hFourier : ((𝓕 f : 𝓢(E, ℂ)) : E → ℂ) = 0 :=
    ConeDyadicResolution.eq_zero_of_symbol_products_zero χ Φ
      (fun ξ => (2 * Real.pi) • ξ) (fun ξ => (𝓕 f : 𝓢(E, ℂ)) ξ) (fun j ξ => by
        rw [← fourier_block, hf j]
        simp)
  have hz : 𝓕 f = (0 : 𝓢(E, ℂ)) := by ext ξ; exact congrFun hFourier ξ
  have hh := congrArg (fun g : 𝓢(E, ℂ) => 𝓕⁻ g) hz
  simpa using hh

end LeanShared.ConeFourierBlocks
