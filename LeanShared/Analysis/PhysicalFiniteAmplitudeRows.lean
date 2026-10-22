module
public import LeanShared.Analysis.PhysicalCylinderPartitionRows

/-! Exact finite-cylinder aggregation with actual compact chart amplitudes.
The amplitudes may be zero extensions of chart-local cutoffs; no globally
continuous unweighted chart decoder or partition is required. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap ENNReal BigOperators
namespace LeanShared.PhysicalFiniteAmplitudeRows
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem identity (output : 𝓢(E,ℂ)) (G : E → E) (continuousG : Continuous G)
    (u : E → ℂ) (continuousU : Continuous u) (g : E → ℂ) (pieces : I → E → ℂ)
    (continuousPieces : ∀ i,Continuous (pieces i))
    (compactPieces : ∀ i,HasCompactSupport (pieces i))
    (reconstruct : ∀ x,g x=∑ i,pieces i x) (x : E) :
    (∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*u (G w)) =
      ∑ i,∫ w,FourierSchwartzKernel.kernel output (x-w)*pieces i w*u (G w) := by
  have integrable (i : I) : Integrable (fun w =>
      FourierSchwartzKernel.kernel output (x-w)*pieces i w*u (G w)) := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    apply HasCompactSupport.intro (compactPieces i)
    intro w hw
    rw [image_eq_zero_of_notMem_tsupport hw,mul_zero,zero_mul]
  simp_rw [reconstruct,Finset.mul_sum,Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => integrable i)

theorem bound (output : 𝓢(E,ℂ)) (G : E → E) (continuousG : Continuous G)
    (u : E → ℂ) (continuousU : Continuous u) (g : E → ℂ) (pieces : I → E → ℂ)
    (continuousPieces : ∀ i,Continuous (pieces i))
    (compactPieces : ∀ i,HasCompactSupport (pieces i))
    (reconstruct : ∀ x,g x=∑ i,pieces i x) (μ : Measure E) (B : I → ℝ≥0∞)
    (rows : ∀ i,(∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*
      pieces i w*u (G w)‖ₑ ∂μ) ≤ B i) :
    (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*u (G w)‖ₑ ∂μ) ≤ ∑ i,B i := by
  have measurable (i : I) : Measurable (fun x => ∫ w,
      FourierSchwartzKernel.kernel output (x-w)*pieces i w*u (G w)) := by
    have joint : Continuous (fun p : E × E => FourierSchwartzKernel.kernel output (p.1-p.2)*
        pieces i p.2*u (G p.2)) := by fun_prop
    exact joint.stronglyMeasurable.integral_prod_right'.measurable
  calc
    _ = ∫⁻ x,‖∑ i,∫ w,FourierSchwartzKernel.kernel output (x-w)*pieces i w*u (G w)‖ₑ ∂μ := by
      congr 1; funext x
      rw [identity output G continuousG u continuousU g pieces continuousPieces compactPieces reconstruct]
    _ ≤ ∫⁻ x,∑ i,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*pieces i w*u (G w)‖ₑ ∂μ :=
      lintegral_mono (fun _ => enorm_sum_le _ _)
    _ = ∑ i,∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*pieces i w*u (G w)‖ₑ ∂μ :=
      lintegral_finsetSum _ (fun i _ => (measurable i).enorm)
    _ ≤ _ := Finset.sum_le_sum (fun i _ => rows i)

end LeanShared.PhysicalFiniteAmplitudeRows
