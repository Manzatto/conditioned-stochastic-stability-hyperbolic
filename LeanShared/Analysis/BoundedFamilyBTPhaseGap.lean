module
public import LeanShared.Analysis.ActualBTFullNonlinkedPhaseGap
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A bounded family of finite-dimensional derivative matrices has a
uniform nonlinked phase gap without any topology on its parameters. Uniform
coercivity and a closed strict cone margin survive passage to the compact
closure of its range. -/
public noncomputable section
open Set
open scoped SchwartzMap ContDiff
namespace LeanShared.BoundedFamilyBTPhaseGap
open ConeDyadicSymbols DyadicFrequencyScale BTLinkedDyadicWeights
variable {E P:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Cp Cm Dp Dm narrow:Set E}

theorem exists_gap (A:P→E→L[ℝ] E) (bound coercive upper lower:ℝ)
    (normBound:∀p,‖A p‖≤bound) (coercivePositive:0<coercive)
    (coerciveBound:∀p v,coercive*‖v‖≤‖A p v‖)
    (closedNarrow:IsClosed narrow)
    (margin:∀v∈narrow,v≠0 → v∈interior Dm)
    (sourceScale:∀r:ℝ,0≤r → ∀v∈Cp,r • v∈Cp)
    (targetScale:∀r:ℝ,0≤r → ∀v∈Dm,r • v∈Dm)
    (action:∀p v,v≠0 → v∉interior Cp → A p v∈narrow)
    (upperPositive:0<upper) (lowerPositive:0<lower)
    (upperBound:∀p v,A p v∉narrow → ‖A p v‖≤upper*‖v‖)
    (lowerBound:∀p v,v∉interior Cp → lower*‖v‖≤‖A p v‖)
    (χ χ':RadialCutoff) (Φ:AngularCutoff Dp Dm)
    (inputCutoffs:ConstructedEnlargedConeSymbols.Cutoffs Cp Cm) :
    ∃δ:ℝ,0<δ ∧ ∃N:ℕ,∀p n l σ τ,N<max n l →
      ¬linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) →
      ∀ξ η:E,symbols χ Φ (n,σ) (((2:ℝ)^n) • ξ)≠0 →
      EnlargedConeDyadicSymbols.symbols χ' inputCutoffs.enlarged inputCutoffs.smooth
        (l,τ) (((2:ℝ)^l) • η)≠0 →
      δ≤‖leftRatio n l • ξ-A p (rightRatio n l • η)‖^2 := by
  have compact:IsCompact (closure (range A)) :=
    (isCompact_closedBall (0:E→L[ℝ]E) bound).of_isClosed_subset isClosed_closure
      (closure_minimal (by
        rintro _ ⟨p,rfl⟩
        simpa only [Metric.mem_closedBall,dist_zero_right] using normBound p) Metric.isClosed_closedBall)
  let X:=closure (range A)
  let :CompactSpace X:=isCompact_iff_compactSpace.mp compact
  have evaluation (v:E):Continuous (fun L:E→L[ℝ]E=>L v):=
    (ContinuousLinearMap.apply ℝ E v).continuous
  have coercivity (L:X) (v:E):coercive*‖v‖≤‖L.val v‖ := by
    exact closure_minimal (by
      rintro _ ⟨p,rfl⟩
      exact coerciveBound p v)
      (isClosed_le continuous_const (evaluation v).norm) L.property
  have injective (L:X):Function.Injective L.val := by
    intro v w equality
    have estimate:=coercivity L (v-w)
    rw [map_sub,equality,sub_self,norm_zero] at estimate
    have zero:‖v-w‖=0 := le_antisymm (by nlinarith) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp zero)
  have coneAction (L:X) (v:E) (nonzero:v≠0) (outside:v∉interior Cp):L.val v∈interior Dm := by
    apply margin (L.val v)
    · exact closure_minimal (by
        rintro _ ⟨p,rfl⟩
        exact action p v nonzero outside) (closedNarrow.preimage (evaluation v)) L.property
    · intro zero
      exact nonzero (injective L (zero.trans (L.val.map_zero).symm))
  have upperEstimate (L:X) (v:E) (outside:L.val v∉interior Dm):‖L.val v‖≤upper*‖v‖ := by
    have alternatives:L.val v∈narrow ∨ ‖L.val v‖≤upper*‖v‖ :=
      closure_minimal (by
        rintro _ ⟨p,rfl⟩
        by_cases member:A p v∈narrow
        · exact Or.inl member
        · exact Or.inr (upperBound p v member))
        ((closedNarrow.preimage (evaluation v)).union
          (isClosed_le (evaluation v).norm continuous_const)) L.property
    rcases alternatives with inside|estimate
    · by_cases zero:L.val v=0
      · rw [zero,norm_zero]
        exact mul_nonneg upperPositive.le (norm_nonneg _)
      · exact False.elim (outside (margin _ inside zero))
    · exact estimate
  have lowerEstimate (L:X) (v:E) (outside:v∉interior Cp):lower*‖v‖≤‖L.val v‖ :=
    closure_minimal (by
      rintro _ ⟨p,rfl⟩
      exact lowerBound p v outside)
      (isClosed_le continuous_const (evaluation v).norm) L.property
  obtain ⟨δ,positiveδ,N,gap⟩:=ActualBTFullNonlinkedPhaseGap.exists_gap
    (fun L:X=>L.val) continuous_subtype_val injective sourceScale targetScale coneAction
    upperPositive lowerPositive upperEstimate lowerEstimate χ χ' Φ inputCutoffs
  exact ⟨δ,positiveδ,N,fun p=>gap ⟨A p,subset_closure (mem_range_self p)⟩⟩
end LeanShared.BoundedFamilyBTPhaseGap
