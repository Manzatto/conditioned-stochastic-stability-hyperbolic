module
public import LeanShared.Analysis.ConeDyadicSymbols
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The genuine cone-kernel family has one fixed finite L1 mass bound,
derived from its finite base symbols and exact dyadic scaling. -/
public noncomputable section
open MeasureTheory Set
open scoped SchwartzMap ENNReal
namespace LeanShared.ConeDyadicSymbols
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Cp Cm : Set E}

theorem exists_uniform_kernel_mass (χ : RadialCutoff) (Φ : AngularCutoff Cp Cm) :
    ∃ A:ℝ,0≤A ∧ ∀ j:ℕ×Bool,
      (∫⁻ x,‖FourierSchwartzKernel.kernel (symbols χ Φ j) x‖ₑ)≤ENNReal.ofReal A := by
  let lowBase : Bool→𝓢(E,ℂ) := fun _=>FourierSchwartzKernel.symbol
    (low χ) (low_hasCompactSupport χ) (low_smooth χ)
  let highBase : Bool→𝓢(E,ℂ) := fun s=>FourierSchwartzKernel.symbol
    (high χ Φ.toFun s) (high_hasCompactSupport χ Φ.toFun s) (high_smooth χ Φ s)
  obtain ⟨A,nonnegative,bound⟩ := DyadicSymbols.exists_uniform_integral_norm_kernel lowBase highBase
  refine ⟨A,nonnegative,?_⟩
  intro j
  rw [←ofReal_integral_norm_eq_lintegral_enorm (FourierSchwartzKernel.kernel (symbols χ Φ j)).integrable]
  exact ENNReal.ofReal_le_ofReal (bound j)
end LeanShared.ConeDyadicSymbols
