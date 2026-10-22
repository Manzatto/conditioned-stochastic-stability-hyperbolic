module
public import LeanShared.Analysis.ConeFourierPointwiseResolution
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The actual localized transfer of finite Fourier resolutions converges
to the actual transfer. Compact amplitudes and the proved uniform input bound
supply dominated convergence; finite block-matrix reconstruction is derived. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace LeanShared.ConeFourierLocalizedTransferResolution
open ConeDyadicSymbols ConeFourierPairingResolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cp Cm : Set E}

theorem converges (χ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (f output : 𝓢(E,ℂ)) (G : E → E) (continuousG : Continuous G)
    (g : E → ℂ) (continuousg : Continuous g) (compactg : HasCompactSupport g) (x : E) :
    Tendsto (fun N => ∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*
      partialSum χ Φ N f (G w)) atTop
      (𝓝 (∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*f (G w))) := by
  let M : ℝ := ∫ ξ,‖(𝓕 f) ξ‖
  let major : E → ℝ := fun w => ‖FourierSchwartzKernel.kernel output (x-w)‖*‖g w‖*M
  have majorContinuous : Continuous major := by dsimp [major]; fun_prop
  have majorCompact : HasCompactSupport major := by
    apply HasCompactSupport.intro compactg
    intro w hw
    dsimp [major]
    rw [image_eq_zero_of_notMem_tsupport hw,norm_zero,mul_zero,zero_mul]
  apply tendsto_integral_of_dominated_convergence (μ := volume) major
    (fun N => (by fun_prop : Continuous (fun w => FourierSchwartzKernel.kernel output (x-w)*g w*
      partialSum χ Φ N f (G w))).aestronglyMeasurable)
    (majorContinuous.integrable_of_hasCompactSupport majorCompact)
    (fun N => ae_of_all _ (fun w => by
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (ConeFourierPointwiseResolution.uniform_bound χ Φ f N (G w)) (by positivity)))
    (ae_of_all _ (fun w => tendsto_const_nhds.mul
      (ConeFourierPointwiseResolution.pointwise_converges χ Φ f (G w))))

theorem finite_expansion (χ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (f output : 𝓢(E,ℂ)) (G : E → E) (continuousG : Continuous G)
    (g : E → ℂ) (continuousg : Continuous g) (compactg : HasCompactSupport g)
    (N : ℕ) (x : E) :
    (∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*partialSum χ Φ N f (G w)) =
      ∑ n ∈ Finset.range (N+1),∑ s : Bool,
        ∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*
          ConeFourierBlocks.block (symbols χ Φ (n,s)) f (G w) := by
  have integrable (n : ℕ) (s : Bool) : Integrable (fun w =>
      FourierSchwartzKernel.kernel output (x-w)*g w*
        ConeFourierBlocks.block (symbols χ Φ (n,s)) f (G w)) := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    apply HasCompactSupport.intro compactg
    intro w hw
    rw [image_eq_zero_of_notMem_tsupport hw,mul_zero,zero_mul]
  simp only [partialSum,sum_apply,Finset.mul_sum]
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ (fun s _ => integrable n s))]
  apply Finset.sum_congr rfl
  intro n _
  exact integral_finsetSum _ (fun s _ => integrable n s)

end LeanShared.ConeFourierLocalizedTransferResolution
