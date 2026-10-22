module
public import ConditionedStochasticStabilityHyperbolic.Global.FullPrefixSameFamilyGap
public import ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies
public import ConditionedStochasticStabilityHyperbolic.Paper.NormalizedGapSimpleWitness
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualHG1DominantOrdering

/-! All HG1 spectral/existence/weak conclusions from the ONE produced full
prefix. This is a constructive final output-consumer, not an ordinary source
record. The actual-source frontend constructs its At and local weak family.
The original live probability is unchanged, and the normalized gap retains
both leading uniqueness clauses and the raw spectral radius. -/
public noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.HG1FullPrefixFamilyConclusion
open LeanShared Paper.LocalConclusions ShiftedFiltrationGeometry ActualFiltrationGrowth
open FiltrationPressureConfinement ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic
open DerivedHG2Application AssembleShiftedPrefixFamilies

variable {X I : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
  (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))
local instance fullPrefixCompact (s : Fin t) :
    CompactSpace (actualPrefix T A Λ ℓ D (terminal s) 0) :=
  isCompact_iff_compactSpace.mp
    (levels_positive_compact T A Λ ℓ 0 D ((terminal s).val + 1)
      (by omega) (by have _h := (terminal s).isLt; omega))

/-- Full leading spectral simplicity, qualified QEM uniqueness and weak
stability hold for exactly the original local family's live pushforward. -/
theorem conclude
    (localFamily : ∀ q, NNReal → ProbabilityMeasure
      (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root q)))
    (s : Fin t) (ν₀ : ProbabilityMeasure
      (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s)))
    (νeq : ProbabilityMeasure X)
    (weak : Tendsto (localFamily s) (𝓝[>] (0 : NNReal)) (𝓝 ν₀))
    (mapLimit : (ν₀ : Measure (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s))).map Subtype.val = (νeq : Measure X))
    (full : actualPrefix T A Λ ℓ D (terminal s) 0 = univ)
    (coreNonempty : (Λ (D.index (selectedIndex ℓ t terminal root s))).Nonempty)
    (zeroA : ∀ ε, 0 < ε → ∀ x, (C ε).killedTransition x A = 0)
    (produced : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε,
      Nonempty (At T A hA Λ ℓ D t terminal root C sf
        (fun q ε => (localFamily q ε : Measure _)) s 0 ε hε))
    (R : ℝ) (hR : 0 < R) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
    ∃ initial : ProbabilityMeasure ↥(Aᶜ), ∃ ν : NNReal → ProbabilityMeasure ↥(Aᶜ),
      (initial : Measure ↥(Aᶜ)).map Subtype.val = (νeq : Measure X) ∧
      Tendsto ν (𝓝[>] (0 : NNReal)) (𝓝 initial) ∧
      ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ _hε : 0 < ε,
        let CL := RestrictedLayerChain.chain (C ε) Aᶜ hA.measurableSet.compl
        let core := {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (selectedIndex ℓ t terminal root s))}
        NormalizedGap CL core (ν ε) ∧
        CL.IsQuasiErgodic (ν ε : Measure ↥(Aᶜ)) ∧ core ⊆ (ν ε : Measure ↥(Aᶜ)).support ∧
        (∀ ζ : Measure ↥(Aᶜ), CL.IsQuasiErgodic ζ → core ⊆ ζ.support →
          ζ = (ν ε : Measure ↥(Aᶜ))) ∧
        Nonempty (SimpleSpectralWitness CL R (ν ε)) := by
  let : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
  let K := closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s)
  let project : K → ↥(Aᶜ) := fun x =>
    ⟨x.val, closedLayer_subset_live T A hA Λ ℓ D _ x.property⟩
  have hp : Continuous project := continuous_subtype_val.subtype_mk _
  have hm := hp.measurable
  let initial := ν₀.map project
  let ν := fun ε => (localFamily s ε).map project
  have mapFamily (ε : NNReal) : (ν ε : Measure ↥(Aᶜ)).map Subtype.val =
      (localFamily s ε : Measure K).map Subtype.val := by
    change ((localFamily s ε : Measure K).map project).map Subtype.val = _
    rw [Measure.map_map measurable_subtype_coe hm]
    rfl
  have initialMap : (initial : Measure ↥(Aᶜ)).map Subtype.val = (νeq : Measure X) := by
    change ((ν₀ : Measure K).map project).map Subtype.val = _
    rw [Measure.map_map measurable_subtype_coe hm]
    exact mapLimit
  refine ⟨initial, ν, initialMap,
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ weak hp, ?_⟩
  filter_upwards [produced] with ε output
  intro hε
  let point := Classical.choice (output hε)
  have same := point.base_identity rfl
  have hP := levels_positive_compact T A Λ ℓ 0 D ((terminal s).val + 1)
    (by omega) (by have _h := (terminal s).isLt; omega)
  obtain ⟨made, gap, mapped⟩ := FullPrefixSameFamilyGap.exists_gap (C ε) (sf ε hε) A hA
    (zeroA ε hε) (actualPrefix T A Λ ℓ D (terminal s) 0) hP full point.data
    (Λ (D.index (selectedIndex ℓ t terminal root s))) point.positive
    ((localFamily s ε : Measure K).map Subtype.val) same
  have measureSame : (made : Measure ↥(Aᶜ)) = (ν ε : Measure ↥(Aᶜ)) :=
    (MeasurableEmbedding.subtype_coe hA.measurableSet.compl).map_injective
      (mapped.trans (mapFamily ε).symm)
  have probabilitySame : made = ν ε := ProbabilityMeasure.toMeasure_injective measureSame
  have actualGap : NormalizedGap (RestrictedLayerChain.chain (C ε) Aᶜ hA.measurableSet.compl)
      {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (selectedIndex ℓ t terminal root s))} (ν ε) :=
    probabilitySame ▸ gap
  have simple := actualGap.simpleWitness R hR
  obtain ⟨liveSF, liveData, product, positive⟩ := actualGap
  let CL := RestrictedLayerChain.chain (C ε) Aᶜ hA.measurableSet.compl
  have positivity (f : ↥(Aᶜ) →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : ↥(Aᶜ)) :
      0 ≤ strongFellerTransferOperator CL liveSF f x := by
    rw [strongFellerTransferOperator_represents]
    exact integral_nonneg hf
  have qem := QuasiErgodic.strongFeller_rankOne_isQuasiErgodic CL liveSF liveData
    (liveData.eigenmeasure positivity) (liveData.eigenmeasure_represents positivity)
    (liveData.eigenvector_nonneg_of_positive positivity)
  have support : {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (selectedIndex ℓ t terminal root s))} ⊆
      (ν ε : Measure ↥(Aᶜ)).support := by
    intro x hx
    apply ComparedLocalQuasiErgodic.mem_support_of_mem_support_map Aᶜ _ x
    rw [mapFamily ε, ← same]
    exact point.support hx
  have liveNonempty : ({x : ↥(Aᶜ) | x.val ∈ Λ (D.index (selectedIndex ℓ t terminal root s))} :
      Set ↥(Aᶜ)).Nonempty := by
    obtain ⟨x, hx⟩ := coreNonempty
    exact ⟨⟨x, Paper.ActualHG1DominantOrdering.index_live T A Λ ℓ D _ hx⟩, hx⟩
  refine ⟨⟨liveSF, liveData, product, positive⟩, product.symm ▸ qem, support, ?_, simple⟩
  intro ζ hζ hsupp
  rw [product]
  exact QuasiErgodic.eq_eigenvectorMeasure_of_basicSet_support CL _
    (strongFellerTransferOperator_represents CL liveSF) liveData (liveData.eigenmeasure positivity)
    (liveData.eigenmeasure_represents positivity) (liveData.eigenvector_nonneg_of_positive positivity)
    _ liveNonempty positive ζ hζ hsupp

end ConditionedStochasticStabilityHyperbolic.Global.HG1FullPrefixFamilyConclusion
