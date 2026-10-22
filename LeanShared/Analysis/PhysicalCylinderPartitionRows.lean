module
public import LeanShared.Analysis.ConeFourierPhysicalRowReconstruction

/-! A genuine finite spatial partition splits the actual transfer integral.
Summing its leaf estimates introduces exactly the sum of cylinder costs,
without an additional count of cylinders in the principal prefactor. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap BigOperators ENNReal
namespace LeanShared.PhysicalCylinderPartitionRows
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem identity (output : 𝓢(E,ℂ)) (G : E → E) (continuousG : Continuous G)
    (u : E → ℂ) (continuousU : Continuous u) (g : E → ℂ)
    (continuousGWeight : Continuous g) (compactGWeight : HasCompactSupport g)
    (β : I → E → ℝ) (continuousβ : ∀ i,Continuous (β i))
    (one : ∀ w,g w≠0 → ∑ i,β i w=1) (x : E) :
    (∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*u (G w)) =
      ∑ i,∫ w,FourierSchwartzKernel.kernel output (x-w)*((β i w:ℂ)*g w)*u (G w) := by
  have integrable (i : I) : Integrable (fun w =>
      FourierSchwartzKernel.kernel output (x-w)*((β i w:ℂ)*g w)*u (G w)) := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    apply HasCompactSupport.intro compactGWeight
    intro w hw
    rw [image_eq_zero_of_notMem_tsupport hw,mul_zero,mul_zero,zero_mul]
  have partition (w : E) : FourierSchwartzKernel.kernel output (x-w)*g w*u (G w) =
      ∑ i,FourierSchwartzKernel.kernel output (x-w)*((β i w:ℂ)*g w)*u (G w) := by
    by_cases h : g w=0
    · simp only [h,mul_zero,zero_mul,Finset.sum_const_zero]
    · calc
        _ = (∑ i,(β i w:ℂ))*(FourierSchwartzKernel.kernel output (x-w)*g w*u (G w)) := by
          rw [←Complex.ofReal_sum,one w h,Complex.ofReal_one,one_mul]
        _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
  simp_rw [partition]
  exact integral_finsetSum _ (fun i _ => integrable i)

theorem bound (output : 𝓢(E,ℂ)) (G : E → E) (continuousG : Continuous G)
    (u : E → ℂ) (continuousU : Continuous u) (g : E → ℂ)
    (continuousGWeight : Continuous g) (compactGWeight : HasCompactSupport g)
    (β : I → E → ℝ) (continuousβ : ∀ i,Continuous (β i))
    (one : ∀ w,g w≠0 → ∑ i,β i w=1) (μ : Measure E) (B : I → ℝ≥0∞)
    (rows : ∀ i,(∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*
      ((β i w:ℂ)*g w)*u (G w)‖ₑ ∂μ) ≤ B i) :
    (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*u (G w)‖ₑ ∂μ) ≤ ∑ i,B i := by
  have measurable (i : I) : Measurable (fun x => ∫ w,
      FourierSchwartzKernel.kernel output (x-w)*((β i w:ℂ)*g w)*u (G w)) := by
    have joint : Continuous (fun p : E×E => FourierSchwartzKernel.kernel output (p.1-p.2)*
        ((β i p.2:ℂ)*g p.2)*u (G p.2)) := by fun_prop
    exact joint.stronglyMeasurable.integral_prod_right'.measurable
  calc
    _ = ∫⁻ x,‖∑ i,∫ w,FourierSchwartzKernel.kernel output (x-w)*
        ((β i w:ℂ)*g w)*u (G w)‖ₑ ∂μ := by
      congr 1; funext x
      rw [identity output G continuousG u continuousU g continuousGWeight compactGWeight β continuousβ one]
    _ ≤ ∫⁻ x,∑ i,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*
        ((β i w:ℂ)*g w)*u (G w)‖ₑ ∂μ := lintegral_mono (fun _ => enorm_sum_le _ _)
    _ = ∑ i,∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*
        ((β i w:ℂ)*g w)*u (G w)‖ₑ ∂μ :=
      lintegral_finsetSum _ (fun i _ => (measurable i).enorm)
    _ ≤ _ := Finset.sum_le_sum (fun i _ => rows i)

end LeanShared.PhysicalCylinderPartitionRows
