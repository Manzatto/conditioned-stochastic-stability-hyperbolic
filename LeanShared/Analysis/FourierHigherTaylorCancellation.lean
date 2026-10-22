module
public import LeanShared.Analysis.PhysicalFourierMoments
public import LeanShared.Analysis.HigherHolderTaylorRemainder

/-! The actual Fourier kernel annihilates the entire higher Taylor
polynomial. Both integrability and cancellation are derived from the symbol. -/
public noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap Topology BigOperators
namespace LeanShared.FourierHigherTaylorCancellation
variable {E ι:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] (b:OrthonormalBasis ι ℝ E)

include b in
theorem integrable_polynomial (σ:𝓢(E,ℂ)) (f:E→ℂ) (n:ℕ) (x:E) (L:E→L[ℝ]E) :
    Integrable (fun y=>FourierSchwartzKernel.kernel σ y*
      HigherHolderTaylorRemainder.polynomial f n x (L y)) := by
  have moment (k:ℕ) : Integrable (fun y=>FourierSchwartzKernel.kernel σ y*
      iteratedFDeriv ℝ k f x (fun _=>L y)) :=
    PhysicalFourierMoments.integrable_moment b σ
      ((iteratedFDeriv ℝ k f x).compContinuousLinearMap (fun _=>L))
  simp only [HigherHolderTaylorRemainder.polynomial,mul_add,Finset.mul_sum,mul_smul_comm]
  apply Integrable.add
  · exact integrable_finsetSum _ fun k _=>
      (moment k).smul ((k.factorial:ℝ)⁻¹)
  · exact ((moment (n+1)).smul
      (∫t in (0:ℝ)..1,(1-t)^n)).smul ((n.factorial:ℝ)⁻¹)

include b in
theorem polynomial_zero (σ:𝓢(E,ℂ)) (zero:∀ᶠξ in 𝓝 (0:E),σ ξ=0)
    (f:E→ℂ) (n:ℕ) (x:E) (L:E→L[ℝ]E) :
    (∫y,FourierSchwartzKernel.kernel σ y*
      HigherHolderTaylorRemainder.polynomial f n x (L y))=0 := by
  have moment (k:ℕ) : Integrable (fun y=>FourierSchwartzKernel.kernel σ y*
      iteratedFDeriv ℝ k f x (fun _=>L y)) :=
    PhysicalFourierMoments.integrable_moment b σ
      ((iteratedFDeriv ℝ k f x).compContinuousLinearMap (fun _=>L))
  simp only [HigherHolderTaylorRemainder.polynomial,mul_add,Finset.mul_sum,mul_smul_comm]
  have int (k:ℕ) := (moment k).smul ((k.factorial:ℝ)⁻¹)
  have top:=((moment (n+1)).smul
      (∫t in (0:ℝ)..1,(1-t)^n)).smul ((n.factorial:ℝ)⁻¹)
  rw [integral_add
    (f:=fun y=>∑k∈Finset.range (n+1),(k.factorial:ℝ)⁻¹ •
      (FourierSchwartzKernel.kernel σ y*iteratedFDeriv ℝ k f x (fun _=>L y)))
    (g:=fun y=>(n.factorial:ℝ)⁻¹ • (∫t in (0:ℝ)..1,(1-t)^n) •
      (FourierSchwartzKernel.kernel σ y*iteratedFDeriv ℝ (n+1) f x (fun _=>L y)))
    (integrable_finsetSum _ fun k _=>int k) top,
    integral_finsetSum (f:=fun k y=>(k.factorial:ℝ)⁻¹ •
      (FourierSchwartzKernel.kernel σ y*iteratedFDeriv ℝ k f x (fun _=>L y))) (Finset.range (n+1)) (fun k _=>int k)]
  have vanish (k:ℕ) : (∫y,FourierSchwartzKernel.kernel σ y*
      iteratedFDeriv ℝ k f x (fun _=>L y))=0 :=
    PhysicalFourierMoments.moment_zero b σ zero
      ((iteratedFDeriv ℝ k f x).compContinuousLinearMap (fun _=>L))
  simp_rw [integral_smul,vanish,smul_zero]
  simp
end LeanShared.FourierHigherTaylorCancellation
