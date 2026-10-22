module
public import LeanShared.Analysis.EnlargedConeBlockReproduction
public import LeanShared.Analysis.BoundedInputPhysicalKernelComposition

/-! The literal localized transfer of a true input Fourier block equals
the two-kernel operator used in the sharp dyadic leaf bound. Neither compact
input-block support nor a kernel representation certificate is assumed. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace LeanShared.ActualInputBlockKernelIdentity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem identity (output original enlarged : 𝓢(E,ℂ))
    (multiplier : ∀ ξ, original ξ*enlarged ξ = original ξ)
    (G : E → E) (continuousG : Continuous G) (g : E → ℂ)
    (continuousg : Continuous g) (compactg : HasCompactSupport g)
    (f : 𝓢(E,ℂ)) (x : E) :
    (∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*
      ConeFourierBlocks.block original f (G w)) =
      ∫ y,(∫ w,g w*FourierSchwartzKernel.kernel output (x-w)*
        FourierSchwartzKernel.kernel enlarged (G w-y))*ConeFourierBlocks.block original f y := by
  let u := ConeFourierBlocks.block original f
  have reproduced : ConeFourierBlocks.block enlarged u = u :=
    EnlargedConeBlockReproduction.block_reproduces original enlarged multiplier f
  have convolution (z : E) :
      (∫ y,FourierSchwartzKernel.kernel enlarged (z-y)*u y) = u z := by
    rw [←ConeFourierBlocks.block_apply, reproduced]
  have actual := BoundedInputPhysicalKernelComposition.identity volume volume G continuousG g
    continuousg compactg u.toBoundedContinuousFunction
    (FourierSchwartzKernel.kernel output).toBoundedContinuousFunction
    (FourierSchwartzKernel.kernel enlarged)
    (FourierSchwartzKernel.kernel enlarged).continuous
    (FourierSchwartzKernel.kernel enlarged).integrable x
  simpa only [SchwartzMap.toBoundedContinuousFunction_apply,convolution] using actual

end LeanShared.ActualInputBlockKernelIdentity
