module
public import LeanShared.Analysis.ConeSymbolRadialBounds
public import LeanShared.Analysis.ConeDyadicResolution

/-! The literal cone multipliers of any two systems have overlapping
frequencies only at neighboring dyadic levels, including level zero. -/
public noncomputable section
open Set
open scoped SchwartzMap BigOperators
namespace LeanShared.ConeSymbolOverlap
open ConeDyadicSymbols
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Cp Cm Dp Dm : Set E}

theorem levels_close (χ ψ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (Ψ : AngularCutoff Dp Dm) (n l : ℕ) (σ τ : Bool) (ξ : E)
    (left : symbols χ Φ (n,σ) ξ≠0) (right : symbols ψ Ψ (l,τ) ξ≠0) :
    n≤l+1 ∧ l≤n+1 := by
  have oneSide (χ ψ : RadialCutoff) {Cp Cm Dp Dm:Set E}
      (Φ : AngularCutoff Cp Cm) (Ψ : AngularCutoff Dp Dm)
      (n l:ℕ) (σ τ:Bool) (left:symbols χ Φ (n,σ) ξ≠0)
      (right:symbols ψ Ψ (l,τ) ξ≠0) : n≤l+1 := by
    by_contra bad
    have big : l+2≤n := by omega
    have positive : n≠0 := by omega
    have low := ConeSymbolRadialBounds.lower χ Φ (n,σ) positive ξ left
    have high := ConeSymbolRadialBounds.upper ψ Ψ (l,τ) ξ right
    have powers : (2:ℝ)^(l+2)≤(2:ℝ)^n := pow_le_pow_right₀ (by norm_num) big
    rw [pow_add] at powers
    norm_num only [pow_succ,pow_zero,mul_one] at powers
    nlinarith
  exact ⟨oneSide χ ψ Φ Ψ n l σ τ left right,oneSide ψ χ Ψ Φ l n τ σ right left⟩

theorem product_zero_of_far (χ ψ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (Ψ : AngularCutoff Dp Dm) (n l : ℕ) (σ τ : Bool) (ξ : E)
    (far : n+1<l ∨ l+1<n) :
    symbols χ Φ (n,σ) ξ*symbols ψ Ψ (l,τ) ξ=0 := by
  by_contra nonzero
  obtain ⟨left,right⟩ := mul_ne_zero_iff.mp nonzero
  have close := levels_close χ ψ Φ Ψ n l σ τ ξ left right
  omega
end LeanShared.ConeSymbolOverlap
