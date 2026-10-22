module
public import LeanShared.Analysis.AnnularDualCutoff
import Mathlib.Tactic

/-! Quantitative support bounds for the already constructed enlarged
input multiplier. -/
public noncomputable section
open Set
open scoped SchwartzMap
namespace LeanShared.AnnularDualCutoff
open ConeDyadicSymbols
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem support_bounds (χ:RadialCutoff) {ξ:E} (nonzero:symbol χ ξ≠0):
    1/4<‖ξ‖ ∧ ‖ξ‖<4:=by
  rw [apply] at nonzero
  constructor
  · by_contra! small
    have h₁:=χ.one (‖ξ‖/2) (by rw [abs_of_nonneg (by positivity)];linarith [norm_nonneg ξ])
    have h₂:=χ.one (4*‖ξ‖) (by rw [abs_of_nonneg (by positivity)];linarith)
    exact nonzero (by simp only [h₁,h₂,sub_self])
  · by_contra! large
    have h₁:=χ.zero (‖ξ‖/2) (by rw [abs_of_nonneg (by positivity)];linarith)
    have h₂:=χ.zero (4*‖ξ‖) (by rw [abs_of_nonneg (by positivity)];linarith)
    exact nonzero (by simp only [h₁,h₂,sub_self])
end LeanShared.AnnularDualCutoff
