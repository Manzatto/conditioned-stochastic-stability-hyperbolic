module
public import LeanShared.Analysis.FourierMultilinearMoments
public import LeanShared.Analysis.ConeFourierBlocks

/-! All polynomial moments of the manuscript's physically normalized Fourier
kernel, obtained from the actual multiplier and its zero neighbourhood. -/
public noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace LeanShared.PhysicalFourierMoments
variable {E ι:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] (b:OrthonormalBasis ι ℝ E)

omit [MeasurableSpace E] [BorelSpace E] in
theorem scaled_zero (σ:𝓢(E,ℂ)) (zero:∀ᶠx in 𝓝 (0:E),σ x=0) :
    ∀ᶠx in 𝓝 (0:E),ConeFourierBlocks.mathlibSymbol σ x=0 := by
  have cont:Continuous (fun x:E=>(2*Real.pi) • x):=continuous_const.smul continuous_id
  simpa only [ConeFourierBlocks.mathlibSymbol_apply,smul_zero] using
    (show Tendsto (fun x:E=>(2*Real.pi) • x) (𝓝 0) (𝓝 0) by
      simpa only [smul_zero] using cont.tendsto (0:E)).eventually zero

include b in
theorem integrable_moment (σ:𝓢(E,ℂ)) {n:ℕ}
    (A:ContinuousMultilinearMap ℝ (fun _:Fin n=>E) ℂ) :
    Integrable (fun y=>FourierSchwartzKernel.kernel σ y*A (fun _=>y)) := by
  rw [ConeFourierBlocks.kernel_eq_fourierInv]
  exact FourierWordMoments.integrable_multilinear_moment b _ A

include b in
theorem moment_zero (σ:𝓢(E,ℂ)) (zero:∀ᶠx in 𝓝 (0:E),σ x=0)
    {n:ℕ} (A:ContinuousMultilinearMap ℝ (fun _:Fin n=>E) ℂ) :
    (∫y,FourierSchwartzKernel.kernel σ y*A (fun _=>y))=0 := by
  rw [ConeFourierBlocks.kernel_eq_fourierInv]
  exact FourierWordMoments.multilinear_moment_zero b _ (scaled_zero σ zero) A
end LeanShared.PhysicalFourierMoments
