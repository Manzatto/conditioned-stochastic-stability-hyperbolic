module
public import LeanShared.Analysis.ConeHolderAnisotropicEmbedding

/-! The literal high-cone base multipliers have the annular support needed
by the constructed dual cutoff; no support certificate is supplied. -/
public noncomputable section
open Set
open scoped SchwartzMap
namespace LeanShared.ConeHolderAnisotropicEmbedding
open ConeDyadicSymbols
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Cplus Cminus : Set E}

theorem high_annulus (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus)
    (s : Bool) (ξ : E) (nonzero : highBase χ Φ s ξ≠0) : 1/2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 := by
  have notSmall : ¬ ‖ξ‖ ≤ 1/2 := by
    intro small
    apply nonzero
    change high χ Φ.toFun s ξ=0
    rw [high,highReal,annular_zero_near_origin χ small,mul_zero,Complex.ofReal_zero]
  have notLarge : ¬ 2 ≤ ‖ξ‖ := by
    intro large
    apply nonzero
    change high χ Φ.toFun s ξ=0
    rw [high,highReal,annular_zero_outside χ large,mul_zero,Complex.ofReal_zero]
  exact ⟨(lt_of_not_ge notSmall).le,(lt_of_not_ge notLarge).le⟩
end LeanShared.ConeHolderAnisotropicEmbedding
