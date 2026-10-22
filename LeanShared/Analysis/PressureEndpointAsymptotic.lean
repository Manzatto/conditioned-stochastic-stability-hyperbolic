module
public import LeanShared.Analysis.PressureCoverFiniteRefinement
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A fixed terminal-alphabet factor disappears at the nth-root pressure
limit. This transfers the N-letter BT upper bound to the actual N-step,
N+1-observation cylinders without asserting identical finite coefficients. -/
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace LeanShared.PressureEndpointAsymptotic

theorem comparison (a b : ℕ → ℝ) (A B C : ℝ) (hC : 0 < C)
    (ha : ∀ N, 0 ≤ a N) (hb : ∀ N, 0 ≤ b N)
    (hab : ∀ᶠ N in atTop, a N ≤ C * b N)
    (hA : Tendsto (fun N : ℕ => a N ^ ((N : ℝ)⁻¹)) atTop (𝓝 A))
    (hB : Tendsto (fun N : ℕ => b N ^ ((N : ℝ)⁻¹)) atTop (𝓝 B)) : A ≤ B := by
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hfactor : Tendsto (fun N : ℕ => C ^ ((N : ℝ)⁻¹)) atTop (𝓝 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp (hinv.const_mul (Real.log C))
    simpa only [Real.rpow_def_of_pos hC, Function.comp_def, mul_zero, Real.exp_zero] using h
  have hup : Tendsto (fun N : ℕ => C ^ ((N : ℝ)⁻¹) * b N ^ ((N : ℝ)⁻¹)) atTop (𝓝 B) := by
    simpa only [one_mul] using hfactor.mul hB
  apply le_of_tendsto_of_tendsto hA hup
  filter_upwards [hab] with N hN
  calc
    a N ^ ((N : ℝ)⁻¹) ≤ (C * b N) ^ ((N : ℝ)⁻¹) :=
      Real.rpow_le_rpow (ha N) hN (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = C ^ ((N : ℝ)⁻¹) * b N ^ ((N : ℝ)⁻¹) := Real.mul_rpow hC.le (hb N)

end LeanShared.PressureEndpointAsymptotic
