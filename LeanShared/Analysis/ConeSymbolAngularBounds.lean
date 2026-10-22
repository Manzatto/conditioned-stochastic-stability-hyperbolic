module
public import LeanShared.Analysis.ConeSymbolRadialBounds

/-! Angular exclusions are proved for the actual high cone symbols;
they are not extra support assumptions. -/
public noncomputable section
open Set
namespace LeanShared.ConeSymbolAngularBounds
open ConeDyadicSymbols
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Cp Cm:Set E}

theorem plus (χ:RadialCutoff) (Φ:AngularCutoff Cp Cm)
    (scale:∀r:ℝ,0≤r → ∀v∈Cm,r • v∈Cm)
    {n:ℕ} (positive:n≠0) {ξ:E} (nonzero:symbols χ Φ (n,true) ξ≠0):ξ∉Cm:=by
  intro inside
  have lo:=ConeSymbolRadialBounds.lower χ Φ (n,true) positive ξ nonzero
  have ξne:ξ≠0:=by
    intro h
    rw [h,norm_zero] at lo
    exact (not_lt_of_ge (by positivity)) lo
  have member:normalized ξ∈Cm:=scale _ (inv_nonneg.mpr (norm_nonneg _)) _ inside
  have angleZero:angle Φ.toFun true ξ=0:=by
    simp only [angle,↓reduceIte,Φ.zero_on _ member (norm_normalized ξne)]
  rw [symbols_apply_of_ne_zero χ Φ _ positive ξ,angleZero,Complex.ofReal_zero,zero_mul] at nonzero
  exact nonzero rfl

theorem minus (χ:RadialCutoff) (Φ:AngularCutoff Cp Cm)
    (scale:∀r:ℝ,0≤r → ∀v∈Cp,r • v∈Cp)
    {n:ℕ} (positive:n≠0) {ξ:E} (nonzero:symbols χ Φ (n,false) ξ≠0):ξ∉Cp:=by
  intro inside
  have lo:=ConeSymbolRadialBounds.lower χ Φ (n,false) positive ξ nonzero
  have ξne:ξ≠0:=by
    intro h
    rw [h,norm_zero] at lo
    exact (not_lt_of_ge (by positivity)) lo
  have member:normalized ξ∈Cp:=scale _ (inv_nonneg.mpr (norm_nonneg _)) _ inside
  have angleZero:angle Φ.toFun false ξ=0:=by
    simp only [angle,Bool.false_eq_true,↓reduceIte,Φ.one_on _ member (norm_normalized ξne),sub_self]
  rw [symbols_apply_of_ne_zero χ Φ _ positive ξ,angleZero,Complex.ofReal_zero,zero_mul] at nonzero
  exact nonzero rfl
end LeanShared.ConeSymbolAngularBounds
