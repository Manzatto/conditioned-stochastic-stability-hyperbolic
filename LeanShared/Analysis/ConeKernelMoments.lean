module
public import LeanShared.Analysis.LowOrderChartPairing
public import LeanShared.Analysis.NormalizedKernelDilation

/-!
Moment bounds for the dyadic cone kernels: the first
moment `∫ |z| |K_{n,σ}(z)| dz` is at most `C₀ 2^{-n}`, and the derivative moment
`∫ |z| |DK_{n,σ}(z)| dz` is bounded uniformly in `n`. Both follow from the exact
dyadic scaling `K_{n,σ}(z) = 2^{dn} K_σ(2^n z)` for `n ≥ 1`.
-/
public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped SchwartzMap
namespace LeanShared.ConeKernelMoments
open FourierSchwartzKernel ConeDyadicSymbols LowOrderChartPairing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cplus Cminus : Set E}

theorem moment_integrable (κ : 𝓢(E, ℂ)) : Integrable (fun z => ‖z‖ * ‖κ z‖) := by
  simpa only [pow_one] using κ.integrable_pow_mul volume 1

theorem derivative_moment_integrable (κ : 𝓢(E, ℂ)) :
    Integrable (fun z => ‖fderiv ℝ κ z‖ * ‖z‖) := by
  have h := (SchwartzMap.fderivCLM ℝ E ℂ κ).integrable_pow_mul volume 1
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only [pow_one, SchwartzMap.fderivCLM_apply]
  ring

theorem moment_dilate (κ : E → ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ z, ‖z‖ * ‖NormalizedKernelDilation.dilate κ r z‖) = r⁻¹ * ∫ z, ‖z‖ * ‖κ z‖ := by
  have h (z : E) : ‖z‖ * ‖NormalizedKernelDilation.dilate κ r z‖ =
      r ^ Module.finrank ℝ E * (r⁻¹ * (‖r • z‖ * ‖κ (r • z)‖)) := by
    simp only [NormalizedKernelDilation.dilate, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      abs_of_pos (pow_pos hr _)]
    field_simp
  simp_rw [h]
  have change := Measure.integral_comp_smul_of_nonneg volume (fun z : E => ‖z‖ * ‖κ z‖) r
    (hR := hr.le)
  rw [integral_const_mul, integral_const_mul, change, smul_eq_mul]
  have hd : r ^ Module.finrank ℝ E ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp

theorem kernel_dilate (σ : 𝓢(E, ℂ)) (r : ℝ) (hr : 0 < r) :
    (kernel (dilateSymbol σ r hr) : E → ℂ) = NormalizedKernelDilation.dilate (kernel σ) r :=
  funext (kernel_dilateSymbol σ r hr)

/-- The first moments of the dyadic cone kernels decay like `2^{-n}`. -/
theorem exists_moment_bound (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ × Bool,
      (∫ z, ‖z‖ * ‖kernel (symbols χ Φ j) z‖) ≤ C * ((2 : ℝ) ^ j.1)⁻¹ := by
  let low := ∑ s : Bool, ∫ z, ‖z‖ * ‖kernel (symbols χ Φ (0, s)) z‖
  let hi := ∑ s : Bool, ∫ z, ‖z‖ * ‖kernel (highSymbol χ Φ s) z‖
  have lowTerm : ∀ s, 0 ≤ ∫ z, ‖z‖ * ‖kernel (symbols χ Φ (0, s)) z‖ := fun s =>
    integral_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hiTerm : ∀ s, 0 ≤ ∫ z, ‖z‖ * ‖kernel (highSymbol χ Φ s) z‖ := fun s =>
    integral_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have low0 : 0 ≤ low := Finset.sum_nonneg fun s _ => lowTerm s
  have hi0 : 0 ≤ hi := Finset.sum_nonneg fun s _ => hiTerm s
  refine ⟨low + hi, add_nonneg low0 hi0, ?_⟩
  rintro ⟨n, s⟩
  by_cases hn : n = 0
  · subst hn
    simp only [pow_zero, inv_one, mul_one]
    calc _ ≤ low := Finset.single_le_sum (f := fun s : Bool =>
          ∫ z, ‖z‖ * ‖kernel (symbols χ Φ (0, s)) z‖) (fun s _ => lowTerm s) (Finset.mem_univ s)
      _ ≤ low + hi := le_add_of_nonneg_right hi0
  · have hr : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
    change (∫ z, ‖z‖ * ‖kernel (symbols χ Φ (n, s)) z‖) ≤ (low + hi) * ((2 : ℝ) ^ n)⁻¹
    rw [symbols_high χ Φ hn s, kernel_dilate _ _ hr, moment_dilate _ hr]
    have single : (∫ z, ‖z‖ * ‖kernel (highSymbol χ Φ s) z‖) ≤ hi :=
      Finset.single_le_sum (f := fun s : Bool => ∫ z, ‖z‖ * ‖kernel (highSymbol χ Φ s) z‖)
        (fun s _ => hiTerm s) (Finset.mem_univ s)
    calc ((2 : ℝ) ^ n)⁻¹ * (∫ z, ‖z‖ * ‖kernel (highSymbol χ Φ s) z‖)
        ≤ ((2 : ℝ) ^ n)⁻¹ * (low + hi) :=
          mul_le_mul_of_nonneg_left (single.trans (le_add_of_nonneg_left low0))
            (inv_nonneg.mpr hr.le)
      _ = (low + hi) * ((2 : ℝ) ^ n)⁻¹ := mul_comm _ _

/-- The derivative moments of the dyadic cone kernels are uniformly bounded. -/
theorem exists_derivative_moment_bound (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ × Bool,
      (∫ z, ‖fderiv ℝ (kernel (symbols χ Φ j)) z‖ * ‖z‖) ≤ C := by
  let low := ∑ s : Bool, ∫ z, ‖fderiv ℝ (kernel (symbols χ Φ (0, s))) z‖ * ‖z‖
  let hi := ∑ s : Bool, ∫ z, ‖fderiv ℝ (kernel (highSymbol χ Φ s)) z‖ * ‖z‖
  have lowTerm : ∀ s, 0 ≤ ∫ z, ‖fderiv ℝ (kernel (symbols χ Φ (0, s))) z‖ * ‖z‖ := fun s =>
    integral_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hiTerm : ∀ s, 0 ≤ ∫ z, ‖fderiv ℝ (kernel (highSymbol χ Φ s)) z‖ * ‖z‖ := fun s =>
    integral_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have low0 : 0 ≤ low := Finset.sum_nonneg fun s _ => lowTerm s
  have hi0 : 0 ≤ hi := Finset.sum_nonneg fun s _ => hiTerm s
  refine ⟨low + hi, add_nonneg low0 hi0, ?_⟩
  rintro ⟨n, s⟩
  by_cases hn : n = 0
  · subst hn
    calc _ ≤ low := Finset.single_le_sum (f := fun s : Bool =>
          ∫ z, ‖fderiv ℝ (kernel (symbols χ Φ (0, s))) z‖ * ‖z‖) (fun s _ => lowTerm s)
          (Finset.mem_univ s)
      _ ≤ low + hi := le_add_of_nonneg_right hi0
  · have hr : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
    change (∫ z, ‖fderiv ℝ (kernel (symbols χ Φ (n, s))) z‖ * ‖z‖) ≤ low + hi
    rw [symbols_high χ Φ hn s, kernel_dilate _ _ hr]
    have scaled := NormalizedKernelDilation.derivative_moment volume
      ((kernel (highSymbol χ Φ s)).smooth 1) hr 1
    simp only [Real.rpow_one] at scaled
    rw [scaled, mul_inv_cancel₀ hr.ne', one_mul]
    exact (Finset.single_le_sum (f := fun s : Bool =>
      ∫ z, ‖fderiv ℝ (kernel (highSymbol χ Φ s)) z‖ * ‖z‖) (fun s _ => hiTerm s)
      (Finset.mem_univ s)).trans (le_add_of_nonneg_left low0)

end LeanShared.ConeKernelMoments
