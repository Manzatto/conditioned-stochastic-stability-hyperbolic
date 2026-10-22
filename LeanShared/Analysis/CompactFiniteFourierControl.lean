module
public import LeanShared.Analysis.CompactFiniteFourierDecay
import all LeanShared.Analysis.CompactFiniteFourierDecay
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Uniform finite-C^n bounds on a fixed compact amplitude support give a
uniform actual Fourier decay constant. Derivative integrals are estimated,
not assumed. -/
public noncomputable section
open Set MeasureTheory
open scoped FourierTransform ContDiff
namespace LeanShared.CompactFiniteFourierDecay
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem derivative_integral_bound {f : E → ℂ} {K : Set E} (compactK : IsCompact K)
    (supported : tsupport f⊆K) (j : ℕ) (B : ℝ)
    (bound : ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    (∫ x, ‖iteratedFDeriv ℝ j f x‖) ≤ B*volume.real K := by
  have equal : (∫ x in K, ‖iteratedFDeriv ℝ j f x‖)=∫ x, ‖iteratedFDeriv ℝ j f x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have zero : iteratedFDeriv ℝ j f x=0 := image_eq_zero_of_notMem_tsupport
      (fun hh => hx (supported (tsupport_iteratedFDeriv_subset j hh)))
    exact norm_eq_zero.mpr zero
  rw [← equal]
  have estimate := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun x : E => ‖iteratedFDeriv ℝ j f x‖) compactK.measure_lt_top
    (fun x hx => by simpa only [norm_norm] using bound x hx)
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using estimate)

theorem derivativeMass_bound {f : E → ℂ} {K : Set E} (compactK : IsCompact K)
    (supported : tsupport f⊆K) (n : ℕ) (B : ℝ)
    (bound : ∀ j ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    derivativeMass f n ≤ (n+1 : ℕ)* (B*volume.real K) := by
  unfold derivativeMass
  apply (Finset.sum_le_sum (fun j hj => derivative_integral_bound compactK supported j B
    (bound j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))))).trans_eq
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

/-- This bound is uniform over arbitrary families sharing a compact support
and their ordinary finite derivative bound. No Fourier decay is supplied. -/
theorem uniform_bound_of_derivatives {f : E → ℂ} {K : Set E} (compactK : IsCompact K)
    (supported : tsupport f⊆K) (n : ℕ) (smooth : ContDiff ℝ (n : ℕ∞) f)
    (B : ℝ) (bound : ∀ j ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ B) (w : E) :
    (1+‖w‖)^n*‖𝓕 f w‖ ≤ 4^n*((n+1 : ℕ)*(B*volume.real K)) := by
  have support : HasCompactSupport f := compactK.of_isClosed_subset (isClosed_tsupport f) supported
  exact (uniform_bound n smooth support w).trans (mul_le_mul_of_nonneg_left
    (derivativeMass_bound compactK supported n B bound) (by positivity))
end LeanShared.CompactFiniteFourierDecay
