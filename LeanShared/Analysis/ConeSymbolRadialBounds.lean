module
public import LeanShared.Analysis.ConeDyadicSymbols
import Mathlib.Tactic

/-! Actual frequency bounds for every constructed cone symbol, including
the literal low-frequency branch. -/
public noncomputable section
open Set
namespace LeanShared.ConeSymbolRadialBounds
open ConeDyadicSymbols
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Cplus Cminus:Set E}

theorem upper (χ:RadialCutoff) (Φ:AngularCutoff Cplus Cminus)
    (j:ℕ × Bool) (ξ:E) (nonzero:symbols χ Φ j ξ≠0):
    ‖ξ‖<2*(2:ℝ)^j.1:=by
  by_cases hj:j.1=0
  · have eq:symbols χ Φ j ξ=(χ.toFun ‖ξ‖:ℂ)/2:=by
      obtain ⟨n,s⟩:=j
      change n=0 at hj
      subst n
      exact symbols_apply_zero χ Φ s ξ
    by_contra! large
    have zero:=χ.zero ‖ξ‖ (by rw [abs_of_nonneg (norm_nonneg _)];simpa [hj] using large)
    exact nonzero (by rw [eq,zero];norm_num)
  · rw [symbols_apply_of_ne_zero χ Φ j hj] at nonzero
    by_contra! large
    have hp:0<(2:ℝ)^j.1:=by positivity
    have size:2≤((2:ℝ)^j.1)⁻¹*‖ξ‖:=by
      apply (le_inv_mul_iff₀ hp).2
      nlinarith
    have h₁:=χ.zero (((2:ℝ)^j.1)⁻¹*‖ξ‖)
      (by rw [abs_of_nonneg (by positivity)];exact size)
    have h₂:=χ.zero ((2*((2:ℝ)^j.1)⁻¹)*‖ξ‖)
      (by rw [abs_of_nonneg (by positivity)];nlinarith)
    exact nonzero (by simp only [h₁,h₂,sub_self,Complex.ofReal_zero,mul_zero])

theorem lower (χ:RadialCutoff) (Φ:AngularCutoff Cplus Cminus)
    (j:ℕ × Bool) (positive:j.1≠0) (ξ:E) (nonzero:symbols χ Φ j ξ≠0):
    (2:ℝ)^j.1/2<‖ξ‖:=by
  rw [symbols_apply_of_ne_zero χ Φ j positive] at nonzero
  by_contra! small
  have hp:0<(2:ℝ)^j.1:=by positivity
  have size:((2:ℝ)^j.1)⁻¹*‖ξ‖≤1/2:=by
    apply (inv_mul_le_iff₀ hp).2
    linarith
  have h₁:=χ.one (((2:ℝ)^j.1)⁻¹*‖ξ‖)
    (by rw [abs_of_nonneg (by positivity)];linarith)
  have h₂:=χ.one ((2*((2:ℝ)^j.1)⁻¹)*‖ξ‖)
    (by rw [abs_of_nonneg (by positivity)];nlinarith)
  exact nonzero (by simp only [h₁,h₂,sub_self,Complex.ofReal_zero,mul_zero])
end LeanShared.ConeSymbolRadialBounds
