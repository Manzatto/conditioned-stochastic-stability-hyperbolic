module
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual finite-order Fourier decay of compactly supported C^n amplitudes.
Only finitely many derivative L1 masses enter, rather than Schwartz bounds. -/
public noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff
namespace LeanShared.CompactFiniteFourierDecay
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def derivativeMass (f : E → ℂ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), ∫ x, ‖iteratedFDeriv ℝ j f x‖

theorem derivativeMass_nonnegative (f : E → ℂ) (n : ℕ) : 0 ≤ derivativeMass f n := by
  apply Finset.sum_nonneg
  intro j _
  exact integral_nonneg (fun _ => norm_nonneg _)

theorem derivative_integrable {f : E → ℂ} {n : ℕ}
    (smooth : ContDiff ℝ (n : ℕ∞) f) (support : HasCompactSupport f)
    (j : ℕ) (hj : j ≤ n) : Integrable (iteratedFDeriv ℝ j f) :=
  (smooth.continuous_iteratedFDeriv (by exact_mod_cast hj)).integrable_of_hasCompactSupport
    (support.iteratedFDeriv j)

theorem power_bound {f : E → ℂ} (n : ℕ)
    (smooth : ContDiff ℝ (n : ℕ∞) f) (support : HasCompactSupport f) (w : E) :
    ‖w‖^n*‖𝓕 f w‖ ≤ 2^n*derivativeMass f n := by
  have masses : ∀ k j : ℕ, k ≤ (0 : ℕ∞) → j ≤ (n : ℕ∞) →
      Integrable (fun x : E => ‖x‖^k*‖iteratedFDeriv ℝ j f x‖) := by
    intro k j hk hj
    have zero : k=0 := by exact_mod_cast (Nat.le_zero.mp (by exact_mod_cast hk))
    subst k
    simp only [pow_zero,one_mul]
    exact (derivative_integrable smooth support j (by exact_mod_cast hj)).norm
  have bound := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := (0 : ℕ∞))
    (N := (n : ℕ∞)) smooth masses (k := 0) (n := n) (by simp) (by simp) w
  simpa only [norm_iteratedFDeriv_zero,pow_zero,one_mul,Nat.cast_zero,mul_zero,zero_add,
    Finset.sum_product,Finset.sum_range_one,Finset.mem_range,derivativeMass] using bound

theorem derivativeMass_mono (f : E → ℂ) {m n : ℕ} (hmn : m ≤ n) :
    derivativeMass f m ≤ derivativeMass f n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hmn 1))
  intro j _ _
  exact integral_nonneg (fun _ => norm_nonneg _)

/-- A global polynomial-decay envelope, including the origin, uses only the
actual first n derivative L1 masses of the amplitude. -/
theorem uniform_bound {f : E → ℂ} (n : ℕ)
    (smooth : ContDiff ℝ (n : ℕ∞) f) (support : HasCompactSupport f) (w : E) :
    (1+‖w‖)^n*‖𝓕 f w‖ ≤ 4^n*derivativeMass f n := by
  have massPos := derivativeMass_nonnegative f n
  have zeroBound : ‖𝓕 f w‖ ≤ derivativeMass f n := by
    have hh := power_bound 0 (smooth.of_le (by simp)) support w
    simp only [pow_zero,one_mul] at hh
    exact hh.trans (derivativeMass_mono f (Nat.zero_le n))
  by_cases small : ‖w‖ ≤ 1
  · have scalar : (1+‖w‖)^n ≤ (4:ℝ)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    exact (mul_le_mul_of_nonneg_right scalar (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left zeroBound (by positivity))
  · have scalar : (1+‖w‖)^n ≤ (2:ℝ)^n*‖w‖^n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    calc
      _ ≤ ((2:ℝ)^n*‖w‖^n)*‖𝓕 f w‖ := mul_le_mul_of_nonneg_right scalar (norm_nonneg _)
      _ = (2:ℝ)^n*(‖w‖^n*‖𝓕 f w‖) := mul_assoc _ _ _
      _ ≤ (2:ℝ)^n*((2:ℝ)^n*derivativeMass f n) :=
        mul_le_mul_of_nonneg_left (power_bound n smooth support w) (by positivity)
      _ = (4:ℝ)^n*derivativeMass f n := by rw [← mul_assoc,← mul_pow]; norm_num

end LeanShared.CompactFiniteFourierDecay
