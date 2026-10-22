module
public import ConditionedStochasticStabilityHyperbolic.Global.LivePrefixNormalizedGap

/-! The full-prefix datum produced by the HG1 construction gives the full
live-space gap for exactly the same probability. This retains simple leading
left/right data for all spectral clauses of global existence, rather than
retaining only its QEM and weak limit. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.FullPrefixSameFamilyGap
open LeanShared ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] in
private theorem transport_set
    (C : AbsorbingMarkovChains.CanonicalChain X) (U V : Set X)
    [CompactSpace U] [CompactSpace V] (hU : MeasurableSet U) (hV : MeasurableSet V)
    (sameSet : U = V) (Λ : Set X) (μ : Measure X)
    (source : ∃ ν : ProbabilityMeasure U,
      Paper.LocalConclusions.NormalizedGap (chain C U hU) {x : U | x.val ∈ Λ} ν ∧
      (ν : Measure U).map Subtype.val = μ) :
    ∃ ν : ProbabilityMeasure V,
      Paper.LocalConclusions.NormalizedGap (chain C V hV) {x : V | x.val ∈ Λ} ν ∧
      (ν : Measure V).map Subtype.val = μ := by
  subst V
  exact source

/-- At the terminal filtration level, removal of the absorbing states
constructs the literal full-live normalized gap and its unchanged ambient
product probability. The eigenfunction/eigenmeasure are produced by the gap. -/
theorem exists_gap
    (C : AbsorbingMarkovChains.CanonicalChain X) (sf : HasStrongFellerKernel C)
    (A : Set X) (hA : IsOpen A) (zeroA : ∀ x, C.killedTransition x A = 0)
    (P : Set X) [CompactSpace P] (hP : IsCompact P) (full : P = univ)
    (d : RankOneSpectralData
      (transferOperator (𝕜 := ℝ) (chain C P hP.measurableSet)
        (strongFeller C sf P hP.measurableSet)) (1 : P →ᵇ ℝ))
    (Λ : Set X) (positive : ∀ x : P, x.val ∈ Λ → 0 < d.eigenvector x)
    (μ : Measure X)
    (same : (productMeasure (chain C P hP.measurableSet)
      (strongFeller C sf P hP.measurableSet) d).map Subtype.val = μ) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
    ∃ ν : ProbabilityMeasure ↥(Aᶜ),
      Paper.LocalConclusions.NormalizedGap (chain C Aᶜ hA.measurableSet.compl)
        {x : ↥(Aᶜ) | x.val ∈ Λ} ν ∧
      (ν : Measure ↥(Aᶜ)).map Subtype.val = μ := by
  subst P
  let : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
  let : CompactSpace ↥((univ : Set X) \ A) :=
    isCompact_iff_compactSpace.mp (hP.inter_right hA.isClosed_compl)
  have made := LivePrefixNormalizedGap.exists_normalizedGap univ A hP hA C sf zeroA d Λ positive
  have live : ((univ : Set X) \ A) = Aᶜ := by ext x; simp
  apply transport_set C ((univ : Set X) \ A) Aᶜ
    (hP.measurableSet.diff hA.measurableSet) hA.measurableSet.compl live Λ μ
  obtain ⟨ν, gap, mapped⟩ := made
  exact ⟨ν, gap, mapped.trans same⟩

end ConditionedStochasticStabilityHyperbolic.Global.FullPrefixSameFamilyGap
