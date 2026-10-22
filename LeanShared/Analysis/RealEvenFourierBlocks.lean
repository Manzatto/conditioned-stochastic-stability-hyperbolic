module

public import LeanShared.Analysis.ConeFourierBlocks
public import LeanShared.Analysis.ConeDyadicSymbols
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Real even Fourier symbols have real kernels, so their actual convolution
blocks commute with complex conjugation. The evenness premise is explicit;
real-valued symbols alone do not imply a real convolution kernel. -/

@[expose] public noncomputable section
open MeasureTheory
open scoped SchwartzMap ComplexConjugate
namespace LeanShared.RealEvenFourierBlocks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def conjugate (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap f

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem conjugate_apply (f : 𝓢(E, ℂ)) (x : E) : conjugate f x = conj (f x) := rfl

theorem kernel_real (σ : 𝓢(E, ℂ))
    (hreal : ∀ ξ, conj (σ ξ) = σ ξ) (heven : ∀ ξ, σ (-ξ) = σ ξ) (x : E) :
    conj (FourierSchwartzKernel.kernel σ x) = FourierSchwartzKernel.kernel σ x := by
  rw [FourierSchwartzKernel.kernel_apply, map_mul, Complex.conj_ofReal, ← integral_conj]
  have hp (ξ : E) :
      conj (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * σ ξ) =
        Complex.exp (Complex.I * (inner ℝ x (-ξ) : ℂ)) * σ (-ξ) := by
    rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
      hreal, heven, inner_neg_right, Complex.ofReal_neg]
    congr 2
    ring
  simp_rw [hp]
  congr 1
  exact integral_neg_eq_self
    (fun ξ : E => Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * σ ξ) volume

theorem block_conjugate (σ f : 𝓢(E, ℂ))
    (hreal : ∀ ξ, conj (σ ξ) = σ ξ) (heven : ∀ ξ, σ (-ξ) = σ ξ) :
    ConeFourierBlocks.block σ (conjugate f) = conjugate (ConeFourierBlocks.block σ f) := by
  ext x
  rw [ConeFourierBlocks.block_apply, conjugate_apply, ConeFourierBlocks.block_apply,
    ← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    dsimp only
    rw [conjugate_apply, map_mul, kernel_real σ hreal heven]

omit [MeasurableSpace E] [BorelSpace E] in
theorem symbols_real {Cp Cm : Set E} (χ : ConeDyadicSymbols.RadialCutoff)
    (Φ : ConeDyadicSymbols.AngularCutoff Cp Cm) (j : ℕ × Bool) (ξ : E) :
    conj (ConeDyadicSymbols.symbols χ Φ j ξ) = ConeDyadicSymbols.symbols χ Φ j ξ := by
  by_cases hn : j.1 = 0
  · obtain ⟨n, b⟩ := j
    change n = 0 at hn
    subst n
    rw [ConeDyadicSymbols.symbols_apply_zero]
    simp only [map_div₀, Complex.conj_ofReal]
    rw [map_ofNat]
  · rw [ConeDyadicSymbols.symbols_apply_of_ne_zero χ Φ j hn]
    simp

omit [MeasurableSpace E] [BorelSpace E] in
theorem symbols_even {Cp Cm : Set E} (χ : ConeDyadicSymbols.RadialCutoff)
    (Φ : ConeDyadicSymbols.AngularCutoff Cp Cm) (hΦ : ∀ ξ, Φ.toFun (-ξ) = Φ.toFun ξ)
    (j : ℕ × Bool) (ξ : E) :
    ConeDyadicSymbols.symbols χ Φ j (-ξ) = ConeDyadicSymbols.symbols χ Φ j ξ := by
  by_cases hn : j.1 = 0
  · obtain ⟨n, b⟩ := j
    change n = 0 at hn
    subst n
    simp only [ConeDyadicSymbols.symbols_apply_zero, norm_neg]
  · simp only [ConeDyadicSymbols.symbols_apply_of_ne_zero χ Φ j hn, norm_neg]
    congr 2
    cases j.2 <;> simp [ConeDyadicSymbols.angle, ConeDyadicSymbols.normalized,
      norm_neg, smul_neg, hΦ]

end LeanShared.RealEvenFourierBlocks
