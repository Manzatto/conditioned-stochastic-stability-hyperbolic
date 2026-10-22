module
public import LeanShared.Analysis.ConstructedEnlargedConeSymbols
public import LeanShared.Analysis.EnlargedDyadicSupport
public import LeanShared.Analysis.RestrictedConePhaseGap
public import LeanShared.Analysis.AngularCrossPhaseGap
public import LeanShared.Analysis.ConeSymbolAngularBounds
public import LeanShared.Analysis.BTNonlinkedRadialRatios

/-! The literal BT nonlinked relation gives a quantitative phase gap for
actual original/output and enlarged/input dyadic symbols. A finite number
of low-frequency mixed pairs is explicitly excluded. -/
public noncomputable section
open Set
open scoped SchwartzMap ContDiff
namespace LeanShared.ActualBTNonlinkedPhaseGap
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
    ∃δ:ℝ,0<δ ∧∃N:ℕ,∀x n l σ τ,n≠0 → l≠0 → N<max n l →
      ¬linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) →
      ∀ξ η:E,symbols χ Φ (n,σ) (((2:ℝ)^n) • ξ)≠0 →
      EnlargedConeDyadicSymbols.symbols χ' inputCutoffs.enlarged inputCutoffs.smooth
        (l,τ) (((2:ℝ)^l) • η)≠0 →
      δ≤‖leftRatio n l • ξ-A x (rightRatio n l • η)‖^2:=by
  obtain ⟨cu,hcu,bu⟩:=RestrictedConePhaseGap.upper_gap targetScale A continuous upperPositive upperBound
  have lowerInverse:∀x v,v∉interior Cp → ‖v‖≤lower⁻¹*‖A x v‖:=by
    intro x v outside
    exact (le_inv_mul_iff₀ lowerPositive).2 (lowerBound x v outside)
  obtain ⟨cl,hcl,bl⟩:=RestrictedConePhaseGap.lower_gap sourceScale A continuous
    (inv_pos.mpr lowerPositive) lowerInverse
  obtain ⟨ca,hca,ba⟩:=AngularCrossPhaseGap.exists_gap Cp Dm A continuous injective
    (fun r hr v hv=>HomogeneousConeInterior.outside_scale sourceScale hr hv)
    (fun r hr v hv=>HomogeneousConeInterior.outside_scale targetScale hr hv) action
  let c:=min cu (min cl ca)
  have hc:0<c:=lt_min hcu (lt_min hcl hca)
  let N:ℕ:=(minusThreshold lower).toNat+(-(plusThreshold upper)).toNat
  refine ⟨c^2,sq_pos_of_pos hc,N,?_⟩
  intro x n l σ τ hn hl large nonlinked ξ η output input
  have an:0<(2:ℝ)^n:=by positivity
  have al:0<(2:ℝ)^l:=by positivity
  have lo:=ConeSymbolRadialBounds.lower χ Φ (n,σ) hn _ output
  have hi:=ConeSymbolRadialBounds.upper χ Φ (n,σ) _ output
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos an] at lo hi
  have ξlo:1/2≤‖ξ‖:=by nlinarith
  have ξhi:‖ξ‖≤2:=by nlinarith
  obtain ⟨ηlo,ηhi,_⟩:=EnlargedDyadicSupport.normalized_support χ' inputCutoffs.enlarged
    inputCutoffs.smooth l τ hl η input
  have hr:leftRatio n l∈Icc (0:ℝ) 1:=⟨div_nonneg an.le (positive n l).le,
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using left_bound n l)⟩
  have hs:rightRatio n l∈Icc (0:ℝ) 1:=⟨div_nonneg al.le (positive n l).le,
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using right_bound n l)⟩
  have hm:max (leftRatio n l) (rightRatio n l)=1:=by
    rcases le_total n l with h|h
    · have eq:rightRatio n l=1:=by simp only [rightRatio,major,max_eq_right h,div_self al.ne']
      rw [eq,max_eq_right hr.2]
    · have eq:leftRatio n l=1:=by simp only [leftRatio,major,max_eq_left h,div_self an.ne']
      rw [eq,max_eq_left hs.2]
  have outputPlus:σ=true → ξ∉interior Dm:=by
    intro eq
    subst σ
    intro inside
    exact ConeSymbolAngularBounds.plus χ Φ targetScale hn output
      (targetScale _ an.le _ (interior_subset inside))
  have inputMinus:τ=false → η∉interior Cp:=by
    intro eq
    subst τ
    exact fun inside=>EnlargedDyadicSupport.normalized_outside χ' inputCutoffs.enlarged
      inputCutoffs.smooth l false hl η input sourceScale inputCutoffs.minusSupport (interior_subset inside)
  have bound:c≤‖leftRatio n l • ξ-A x (rightRatio n l • η)‖:=by
    cases σ with
    | false =>
      cases τ with
      | false =>
        have levels:(n:ℤ)<(l:ℤ)+minusThreshold lower:=by
          by_contra! levels
          exact nonlinked (Or.inr (Or.inl ⟨rfl,rfl,levels⟩))
        exact (min_le_right cu (min cl ca) |>.trans (min_le_left cl ca)).trans
          (bl x ξ η _ _ (inputMinus rfl) ξlo ξhi ηlo.le ηhi.le hr hs hm
            (BTNonlinkedRadialRatios.lower_ratio lowerPositive n l levels))
      | true =>
        have hn':(n:ℤ)<minusThreshold lower:=by
          by_contra! levels
          exact nonlinked (Or.inr (Or.inr ⟨rfl,rfl,Or.inl levels⟩))
        have hl':(l:ℤ)< -(plusThreshold upper):=by
          by_contra! levels
          exact nonlinked (Or.inr (Or.inr ⟨rfl,rfl,Or.inr levels⟩))
        dsimp only [N] at large
        omega
    | true =>
      cases τ with
      | false =>
        exact (min_le_right cu (min cl ca) |>.trans (min_le_right cl ca)).trans
          (ba x ξ η _ _ (outputPlus rfl) (inputMinus rfl)
            (by linarith) (by linarith) ηlo.le ηhi.le hr hs hm)
      | true =>
        have levels:(l:ℤ)+plusThreshold upper<(n:ℤ):=by
          by_contra! levels
          exact nonlinked (Or.inl ⟨rfl,rfl,levels⟩)
        exact (min_le_left cu (min cl ca)).trans
          (bu x ξ η _ _ (outputPlus rfl) ξlo ξhi ηlo.le ηhi.le hr hs hm
            (BTNonlinkedRadialRatios.upper_ratio upperPositive n l levels))
  nlinarith [norm_nonneg (leftRatio n l • ξ-A x (rightRatio n l • η))]
end LeanShared.ActualBTNonlinkedPhaseGap
