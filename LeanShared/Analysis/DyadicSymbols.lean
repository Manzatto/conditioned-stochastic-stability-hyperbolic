module

public import LeanShared.Analysis.FourierSchwartzKernel

/-!
# Actual dyadic dilation symbols and uniformly integrable Fourier kernels

The low-frequency and annular base symbols are genuine smooth compact-support
inputs. All high-frequency symbols are constructed by inverse dyadic dilation.
The Fourier kernel scaling and uniform ambient `L1` bound are proved.

Identifying the bases with the radial/angular cone cutoffs of the manuscript,
their annular supports, and their partition of unity remains separate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap ContDiff

namespace LeanShared.DyadicSymbols

variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A true dyadic symbol; its low-frequency member is kept separately. -/
def symbol (low high : S → 𝓢(E, ℂ)) (j : ℕ × S) : 𝓢(E, ℂ) :=
  if j.1 = 0 then low j.2 else
    FourierSchwartzKernel.dilateSymbol (high j.2) ((2 : ℝ) ^ j.1) (pow_pos (by norm_num) _)

def kernel (low high : S → 𝓢(E, ℂ)) (j : ℕ × S) : 𝓢(E, ℂ) :=
  FourierSchwartzKernel.kernel (symbol low high j)

omit [MeasurableSpace E] [BorelSpace E] in
theorem symbol_apply_of_ne_zero (low high : S → 𝓢(E, ℂ)) (j : ℕ × S)
    (hj : j.1 ≠ 0) (ξ : E) : symbol low high j ξ = high j.2 (((2 : ℝ) ^ j.1)⁻¹ • ξ) := by
  simp only [symbol, hj, ↓reduceIte, FourierSchwartzKernel.dilateSymbol_apply]

omit [MeasurableSpace E] [BorelSpace E] in
theorem symbol_hasCompactSupport (low high : S → 𝓢(E, ℂ))
    (hlow : ∀ s, HasCompactSupport (low s : E → ℂ))
    (hhigh : ∀ s, HasCompactSupport (high s : E → ℂ)) (j : ℕ × S) :
    HasCompactSupport (symbol low high j : E → ℂ) := by
  by_cases hj : j.1 = 0
  · simpa only [symbol, hj, ↓reduceIte] using hlow j.2
  · simpa only [symbol, hj, ↓reduceIte] using
      FourierSchwartzKernel.dilateSymbol_hasCompactSupport (high j.2) (hhigh j.2)
        ((2 : ℝ) ^ j.1) (pow_pos (by norm_num) _)

theorem kernel_apply_of_ne_zero (low high : S → 𝓢(E, ℂ)) (j : ℕ × S)
    (hj : j.1 ≠ 0) (x : E) :
    kernel low high j x = (((2 : ℝ) ^ j.1) ^ Module.finrank ℝ E) •
      FourierSchwartzKernel.kernel (high j.2) (((2 : ℝ) ^ j.1) • x) := by
  simp only [kernel, symbol, hj, ↓reduceIte, FourierSchwartzKernel.kernel_dilateSymbol]

theorem integral_norm_kernel_of_ne_zero (low high : S → 𝓢(E, ℂ)) (j : ℕ × S)
    (hj : j.1 ≠ 0) :
    (∫ x : E, ‖kernel low high j x‖) = ∫ x : E, ‖FourierSchwartzKernel.kernel (high j.2) x‖ := by
  simp only [kernel, symbol, hj, ↓reduceIte, FourierSchwartzKernel.integral_norm_kernel_dilateSymbol]

theorem kernel_integrable (low high : S → 𝓢(E, ℂ)) (j : ℕ × S) :
    Integrable (kernel low high j) := (kernel low high j).integrable

/-- The paper's uniform ambient `L1` bound follows from finitely many fixed bases. -/
theorem exists_uniform_integral_norm_kernel [Fintype S] (low high : S → 𝓢(E, ℂ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j : ℕ × S, (∫ x : E, ‖kernel low high j x‖) ≤ A := by
  classical
  let a : S → ℝ := fun s => ∫ x : E, ‖FourierSchwartzKernel.kernel (low s) x‖
  let b : S → ℝ := fun s => ∫ x : E, ‖FourierSchwartzKernel.kernel (high s) x‖
  have ha : ∀ s, 0 ≤ a s := fun _ => integral_nonneg fun x => norm_nonneg _
  have hb : ∀ s, 0 ≤ b s := fun _ => integral_nonneg fun x => norm_nonneg _
  refine ⟨∑ s, (a s + b s), Finset.sum_nonneg (fun s _ => add_nonneg (ha s) (hb s)), ?_⟩
  intro j
  have hsingle : a j.2 + b j.2 ≤ ∑ s, (a s + b s) :=
    Finset.single_le_sum (fun s _ => add_nonneg (ha s) (hb s)) (Finset.mem_univ _)
  by_cases hj : j.1 = 0
  · have heq : (∫ x : E, ‖kernel low high j x‖) = a j.2 := by simp only [kernel, symbol, hj, ↓reduceIte, a]
    rw [heq]
    exact (le_add_of_nonneg_right (hb j.2)).trans hsingle
  · rw [integral_norm_kernel_of_ne_zero low high j hj]
    exact (le_add_of_nonneg_left (ha j.2)).trans hsingle

/-- Genuine compactly supported smooth base multipliers produce actual dyadic symbols. -/
def symbolsFromMultipliers (low high : S → E → ℂ)
    (hlow : ∀ s, HasCompactSupport (low s)) (hhigh : ∀ s, HasCompactSupport (high s))
    (hslow : ∀ s, ContDiff ℝ ∞ (low s)) (hshigh : ∀ s, ContDiff ℝ ∞ (high s)) :
    ℕ × S → 𝓢(E, ℂ) :=
  symbol (fun s => FourierSchwartzKernel.symbol (low s) (hlow s) (hslow s))
    (fun s => FourierSchwartzKernel.symbol (high s) (hhigh s) (hshigh s))

omit [MeasurableSpace E] [BorelSpace E] in
theorem symbolsFromMultipliers_hasCompactSupport (low high : S → E → ℂ)
    (hlow : ∀ s, HasCompactSupport (low s)) (hhigh : ∀ s, HasCompactSupport (high s))
    (hslow : ∀ s, ContDiff ℝ ∞ (low s)) (hshigh : ∀ s, ContDiff ℝ ∞ (high s)) (j : ℕ × S) :
    HasCompactSupport (symbolsFromMultipliers low high hlow hhigh hslow hshigh j : E → ℂ) :=
  symbol_hasCompactSupport
    (fun s => FourierSchwartzKernel.symbol (low s) (hlow s) (hslow s))
    (fun s => FourierSchwartzKernel.symbol (high s) (hhigh s) (hshigh s)) hlow hhigh j

/-- The genuinely constructed manuscript-convention inverse Fourier kernels. -/
def fromMultipliers (low high : S → E → ℂ)
    (hlow : ∀ s, HasCompactSupport (low s)) (hhigh : ∀ s, HasCompactSupport (high s))
    (hslow : ∀ s, ContDiff ℝ ∞ (low s)) (hshigh : ∀ s, ContDiff ℝ ∞ (high s)) :
    ℕ × S → 𝓢(E, ℂ) :=
  fun j => FourierSchwartzKernel.kernel (symbolsFromMultipliers low high hlow hhigh hslow hshigh j)

theorem fromMultipliers_uniform_L1 [Fintype S] (low high : S → E → ℂ)
    (hlow : ∀ s, HasCompactSupport (low s)) (hhigh : ∀ s, HasCompactSupport (high s))
    (hslow : ∀ s, ContDiff ℝ ∞ (low s)) (hshigh : ∀ s, ContDiff ℝ ∞ (high s)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j : ℕ × S,
      (∫ x : E, ‖fromMultipliers low high hlow hhigh hslow hshigh j x‖) ≤ A :=
  exists_uniform_integral_norm_kernel
    (fun s => FourierSchwartzKernel.symbol (low s) (hlow s) (hslow s))
    (fun s => FourierSchwartzKernel.symbol (high s) (hhigh s) (hshigh s))

end LeanShared.DyadicSymbols
