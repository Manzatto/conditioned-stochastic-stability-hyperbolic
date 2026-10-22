module
public import LeanShared.Analysis.CompactFourierFubini
import Mathlib.Tactic

/-! Finite actual compact frequency kernels can be summed before or
after Fourier inversion, with no additional integrability premise. -/
public noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace LeanShared.CompactFourierFiniteSum
variable {Z ι:Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z] [Fintype ι]

theorem fourier_sum (f:ι→Z→ℂ) (fc:∀i,Continuous (f i))
    (fs:∀i,HasCompactSupport (f i)) (z:Z):
    𝓕 (fun ζ=>∑i,f i ζ) z=∑i,𝓕 (f i) z:=by
  simp only [Real.fourier_eq',smul_eq_mul,Finset.mul_sum]
  apply integral_finsetSum
  intro i _
  have cw:Continuous (fun ζ:Z=>Complex.exp ((-2*Real.pi*inner ℝ ζ z:ℝ)*Complex.I)):=by fun_prop
  exact (cw.mul (fc i)).integrable_of_hasCompactSupport (fs i).mul_left

theorem norm_bound (f:ι→Z→ℂ) (fc:∀i,Continuous (f i))
    (fs:∀i,HasCompactSupport (f i)) (z:Z) (C:ι→ℝ) (w:ℝ)
    (bound:∀i,‖𝓕 (f i) z‖≤C i*w):
    ‖𝓕 (fun ζ=>∑i,f i ζ) z‖≤(∑i,C i)*w:=by
  rw [fourier_sum f fc fs z]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _=>bound i)).trans_eq (Finset.sum_mul ..).symm)
end LeanShared.CompactFourierFiniteSum
