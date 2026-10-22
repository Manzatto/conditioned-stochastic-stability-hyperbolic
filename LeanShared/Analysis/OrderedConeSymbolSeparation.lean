module
public import LeanShared.Analysis.ConeSymbolOverlap

/-! Ordered cone systems exclude the only high-frequency sign interaction
that would lose anisotropic regularity: target plus against source minus. -/
public noncomputable section
open Set
namespace LeanShared.OrderedConeSymbolSeparation
open ConeDyadicSymbols
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Cp Cm Dp Dm : Set E}

theorem plus_minus_zero (χ ψ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (Ψ : AngularCutoff Dp Dm)
    (ordered : ∀ ξ:E,‖ξ‖=1→ξ∉Dp→ξ∈Cm)
    (n l : ℕ) (positiveN : n≠0) (positiveL : l≠0) (ξ : E) :
    symbols χ Φ (n,true) ξ*symbols ψ Ψ (l,false) ξ=0 := by
  by_cases zero : ξ=0
  · subst ξ
    have leftZero : symbols χ Φ (n,true) (0:E)=0 := by
      by_contra nonzero
      have low := ConeSymbolRadialBounds.lower χ Φ (n,true) positiveN 0 nonzero
      have positive : 0<(2:ℝ)^n/2 := by positivity
      simp only [norm_zero] at low
      linarith
    rw [leftZero,zero_mul]
  · have unit := norm_normalized zero
    by_cases inside : normalized ξ∈Dp
    · have one := Ψ.one_on (normalized ξ) inside unit
      rw [symbols_apply_of_ne_zero ψ Ψ (l,false) positiveL]
      simp only [angle,Bool.false_eq_true,ite_false,one,sub_self,Complex.ofReal_zero,zero_mul,mul_zero]
    · have vanish := Φ.zero_on (normalized ξ) (ordered _ unit inside) unit
      rw [symbols_apply_of_ne_zero χ Φ (n,true) positiveN]
      simp only [angle,ite_true,vanish,Complex.ofReal_zero,zero_mul]
end LeanShared.OrderedConeSymbolSeparation
