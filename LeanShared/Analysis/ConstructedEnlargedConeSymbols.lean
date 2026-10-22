module
public import LeanShared.Analysis.EnlargedConeDyadicSymbols

/-! Fully constructed original and enlarged cone cutoffs. The support
collars and exact multiplier identity have checked producers. -/
public noncomputable section
open Set
open scoped ContDiff SchwartzMap
namespace LeanShared.ConstructedEnlargedConeSymbols
open ConeDyadicSymbols
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

structure Cutoffs (Cp Cm:Set E) where
  original:AngularCutoff Cp Cm
  enlarged:Bool→E→ℝ
  smooth:∀s,ContDiff ℝ ∞ (enlarged s)
  plusSupport:tsupport (enlarged true)⊆Cmᶜ
  minusSupport:tsupport (enlarged false)⊆Cpᶜ
  one:∀s ξ,‖ξ‖=1 → (if s then original.toFun ξ else 1-original.toFun ξ)≠0 → enlarged s ξ=1

@[expose] def construct {Cp Cm:Set E} (closedP:IsClosed Cp) (closedM:IsClosed Cm)
    (disjoint:∀ξ∈Cp,‖ξ‖=1 → ξ∉Cm):Cutoffs Cp Cm:=by
  apply Classical.choice
  obtain ⟨Φ,plus,minus,_,smoothP,smoothM,_,_,_,_,supportP,supportM,oneP,oneM⟩:=
    ConstructedBufferedAngularCutoff.exists_enlargements closedP closedM disjoint
  let ψ:Bool→E→ℝ:=fun s=>if s then plus else minus
  have smooth:∀s,ContDiff ℝ ∞ (ψ s):=by intro s;cases s <;> simp only [ψ,Bool.false_eq_true,↓reduceIte] <;> assumption
  refine ⟨⟨Φ,ψ,smooth,supportP,supportM,?_⟩⟩
  intro s ξ unit nonzero
  cases s
  · exact oneM ξ unit nonzero
  · exact oneP ξ unit nonzero

variable [MeasurableSpace E] [BorelSpace E]
omit [MeasurableSpace E] [BorelSpace E] in
theorem Cutoffs.multiplier_identity {Cp Cm:Set E} (cutoffs:Cutoffs Cp Cm)
    (χ:RadialCutoff) (j:ℕ × Bool) (ξ:E):
    ConeDyadicSymbols.symbols χ cutoffs.original j ξ*
      EnlargedConeDyadicSymbols.symbols χ cutoffs.enlarged cutoffs.smooth j ξ=
    ConeDyadicSymbols.symbols χ cutoffs.original j ξ:=
  EnlargedConeDyadicSymbols.multiplier_identity χ cutoffs.original cutoffs.enlarged cutoffs.smooth cutoffs.one j ξ
end LeanShared.ConstructedEnlargedConeSymbols
