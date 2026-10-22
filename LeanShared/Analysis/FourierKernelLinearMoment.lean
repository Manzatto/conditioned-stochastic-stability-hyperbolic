module
public import LeanShared.Analysis.FourierKernelFirstMoment
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! All actual real-linear scalar first moments vanish. The passage from
real Fourier directions to complex amplitudes uses proved Riesz duality. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace LeanShared.FourierSchwartzKernel
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_linear_kernel (σ:𝓢(E,ℂ)) (ℓ:E→L[ℝ]ℂ) :
    Integrable (fun y=>kernel σ y*ℓ y) := by
  have moment : Integrable (fun y=>‖y‖*‖kernel σ y‖) := by
    simpa only [pow_one] using (kernel σ).integrable_pow_mul volume 1
  apply (moment.const_mul ‖ℓ‖).mono'
  · exact ((kernel σ).continuous.mul ℓ.continuous).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (ℓ.le_opNorm y) (norm_nonneg _)).trans_eq (by ring)

theorem linear_first_moment (σ:𝓢(E,ℂ))
    (zero:fderiv ℝ (fun ξ=>ConeFourierBlocks.mathlibSymbol σ ξ) 0=0) (ℓ:E→L[ℝ]ℂ) :
    (∫ y,kernel σ y*ℓ y)=0 := by
  let vr := (InnerProductSpace.toDual ℝ E).symm (Complex.reCLM.comp ℓ)
  let vi := (InnerProductSpace.toDual ℝ E).symm (Complex.imCLM.comp ℓ)
  have repr (y:E) : ℓ y=(inner ℝ y vr:ℂ)+(inner ℝ y vi:ℂ)*Complex.I := by
    have real : inner ℝ y vr=(ℓ y).re := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have imag : inner ℝ y vi=(ℓ y).im := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    rw [real,imag]
    exact (Complex.re_add_im (ℓ y)).symm
  have integrableInner (v:E) : Integrable (fun y=>kernel σ y*(inner ℝ y v:ℂ)) := by
    convert integrable_linear_kernel σ (Complex.ofRealCLM.comp (innerSL ℝ v)) using 1
    funext y
    simp only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,innerSL_apply_apply ℝ,real_inner_comm]
  have integralInner (v:E) : (∫ y,kernel σ y*(inner ℝ y v:ℂ))=0 := by
    calc
      _ = ∫ y,(inner ℝ y v:ℂ)*kernel σ y := integral_congr_ae (ae_of_all _ fun y=>mul_comm _ _)
      _ = 0 := first_moment σ zero v
  have integrand : (fun y=>kernel σ y*ℓ y)=fun y=>
      kernel σ y*(inner ℝ y vr:ℂ)+(kernel σ y*(inner ℝ y vi:ℂ))*Complex.I := by
    funext y
    rw [repr,mul_add,←mul_assoc]
  rw [integrand,integral_add (integrableInner vr) ((integrableInner vi).mul_const Complex.I),
    integral_mul_const,integralInner vr,integralInner vi,zero_mul,zero_add]
end LeanShared.FourierSchwartzKernel
