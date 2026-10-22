module
public import LeanShared.Analysis.ActualBTNonlinkedPhaseGap
public import LeanShared.Analysis.NormalizedLowFrequencyPhaseGap

/-! Complete BT nonlinked separation for the actual cone multipliers,
including the low-frequency branches. Only a constructed finite square
of dyadic levels is reserved for the weak remainder. -/
public noncomputable section
open Set
open scoped SchwartzMap ContDiff
namespace LeanShared.ActualBTFullNonlinkedPhaseGap
open ConeDyadicSymbols DyadicFrequencyScale BTLinkedDyadicWeights
variable {E X:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace E] [BorelSpace E] {Cp Cm Dp Dm:Set E}

omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_gap (A:X→E→L[ℝ] E) (continuous:Continuous A)
    (injective:∀x,Function.Injective (A x))
    (sourceScale:∀r:ℝ,0≤r → ∀v∈Cp,r • v∈Cp)
    (targetScale:∀r:ℝ,0≤r → ∀v∈Dm,r • v∈Dm)
    (action:∀x v,v≠0 → v∉interior Cp → A x v∈interior Dm)
    {upper lower:ℝ} (upperPositive:0<upper) (lowerPositive:0<lower)
    (upperBound:∀x v,A x v∉interior Dm → ‖A x v‖≤upper*‖v‖)
    (lowerBound:∀x v,v∉interior Cp → lower*‖v‖≤‖A x v‖)
    (χ χ':RadialCutoff) (Φ:AngularCutoff Dp Dm)
    (inputCutoffs:ConstructedEnlargedConeSymbols.Cutoffs Cp Cm):
    ∃δ:ℝ,0<δ ∧∃N:ℕ,∀x n l σ τ,N<max n l →
      ¬linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) →
      ∀ξ η:E,symbols χ Φ (n,σ) (((2:ℝ)^n) • ξ)≠0 →
      EnlargedConeDyadicSymbols.symbols χ' inputCutoffs.enlarged inputCutoffs.smooth
        (l,τ) (((2:ℝ)^l) • η)≠0 →
      δ≤‖leftRatio n l • ξ-A x (rightRatio n l • η)‖^2:=by
  obtain ⟨δh,hδh,Nh,highGap⟩:=ActualBTNonlinkedPhaseGap.exists_gap A continuous injective
    sourceScale targetScale action upperPositive lowerPositive upperBound lowerBound χ χ' Φ inputCutoffs
  obtain ⟨δl,hδl,Nl,lowGap⟩:=NormalizedLowFrequencyPhaseGap.exists_gap A continuous injective
  refine ⟨min δh δl,lt_min hδh hδl,max Nh Nl,?_⟩
  intro x n l σ τ large nonlinked ξ η output input
  by_cases low:n=0 ∨l=0
  · have an:0<(2:ℝ)^n:=by positivity
    have upperξ:=ConeSymbolRadialBounds.upper χ Φ (n,σ) _ output
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos an] at upperξ
    have ξhi:‖ξ‖≤2:=by nlinarith
    have ηhi:=EnlargedDyadicSupport.normalized_upper χ' inputCutoffs.enlarged
      inputCutoffs.smooth l τ η input
    have ξlo:n≠0 → 1/2≤‖ξ‖:=by
      intro positive
      have lowerξ:=ConeSymbolRadialBounds.lower χ Φ (n,σ) positive _ output
      simp only [norm_smul,Real.norm_eq_abs,abs_of_pos an] at lowerξ
      nlinarith
    have ηlo:l≠0 → 1/4≤‖η‖:=by
      intro positive
      exact (EnlargedDyadicSupport.normalized_support χ' inputCutoffs.enlarged
        inputCutoffs.smooth l τ positive η input).1.le
    exact (min_le_right δh δl).trans (lowGap x n l low
      ((le_max_right Nh Nl).trans_lt large) ξ η ξhi ηhi ξlo ηlo)
  · have hn:n≠0:=by tauto
    have hl:l≠0:=by tauto
    exact (min_le_left δh δl).trans (highGap x n l σ τ hn hl
      ((le_max_left Nh Nl).trans_lt large) nonlinked ξ η output input)
end LeanShared.ActualBTFullNonlinkedPhaseGap
