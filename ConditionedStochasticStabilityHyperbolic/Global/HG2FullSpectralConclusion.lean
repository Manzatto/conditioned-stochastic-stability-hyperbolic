module
public import ConditionedStochasticStabilityHyperbolic.Global.FullPrefixSameFamilyGap
public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Conclusions
public import ConditionedStochasticStabilityHyperbolic.Paper.NormalizedGapSimpleWitness

/-! The generated HG2 family retains all leading spectral clauses at its
full first prefix, for precisely the same live quasi-ergodic probability. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.HG2FullSpectralConclusion
open LeanShared Paper.LocalConclusions ShiftedFiltrationGeometry ActualFiltrationGrowth
open ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic DerivedHG2Application
variable {X I : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
  (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))
  (d : Families T A hA Λ ℓ D t terminal root C sf)
local instance prefixCompact (s : Fin t) : CompactSpace (actualPrefix T A Λ ℓ D (terminal s) 0) :=
  isCompact_iff_compactSpace.mp
    (levels_positive_compact T A Λ ℓ 0 D ((terminal s).val + 1)
      (by omega) (by have _h := (terminal s).isLt; omega))

theorem same_family_normalizedGap (s : Fin t)
    (fullSize : (terminal s).val + 1 = ℓ) (ε : NNReal) (hε : 0 < ε)
    (hs : ε < d.window s 0) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
    NormalizedGap (chain (C ε) Aᶜ hA.measurableSet.compl)
      {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (DerivedHG2Basins.originalIndex (root s)))}
      (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε)  := by
  let : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
  have full : actualPrefix T A Λ ℓ D (terminal s) 0 = univ := by
    change levels T A Λ ℓ 0 D ((terminal s).val + 1) = univ
    rw [fullSize]
    change shiftedFiltration T 0 A D.levels ℓ = univ
    rw [shiftedFiltration_pos T 0 A D.levels (by have _h := (terminal s).isLt; omega)]
    simpa only [Function.iterate_zero, id_eq, Set.preimage_id_eq] using D.terminal
  have mapped :
      (productMeasure (chain (C ε) (actualPrefix T A Λ ℓ D (terminal s) 0)
        (ambient_levels_measurable T A hA Λ ℓ 0 D ((terminal s).val + 1)))
        (strongFeller (C ε) (sf ε hε) (actualPrefix T A Λ ℓ D (terminal s) 0)
          (ambient_levels_measurable T A hA Λ ℓ 0 D ((terminal s).val + 1)))
        (d.data s 0 ε hε hs)).map Subtype.val =
      (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)).map Subtype.val := by
    rw [d.base_product_identity s ε hε hs]
    exact (congrArg (fun ν : ProbabilityMeasure X => (ν : Measure X))
      (liveLaw_map T A hA Λ ℓ D t terminal root C sf d s ε)).symm
  obtain ⟨ν, gap, mapν⟩ := FullPrefixSameFamilyGap.exists_gap (C ε) (sf ε hε) A hA
    (d.zero_absorbing ε hε) (actualPrefix T A Λ ℓ D (terminal s) 0)
    (levels_positive_compact T A Λ ℓ 0 D ((terminal s).val + 1)
      (by omega) (by have _h := (terminal s).isLt; omega)) full
    (d.data s 0 ε hε hs) (Λ (D.index (DerivedHG2Basins.originalIndex (root s))))
    (d.core_positive s 0 ε hε hs) _ mapped
  have same : ν = liveLaw T A hA Λ ℓ D t terminal root C sf d s ε :=
    ProbabilityMeasure.toMeasure_injective
      ((MeasurableEmbedding.subtype_coe hA.measurableSet.compl).map_injective mapν)
  exact same ▸ gap

theorem same_family_simpleWitness (s : Fin t)
    (fullSize : (terminal s).val + 1 = ℓ) (R : ℝ) (hR : 0 < R)
    (ε : NNReal) (hε : 0 < ε) (hs : ε < d.window s 0) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
    Nonempty (SimpleSpectralWitness (chain (C ε) Aᶜ hA.measurableSet.compl) R
      (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε)) := by
  let : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
  exact (same_family_normalizedGap T A hA Λ ℓ D t terminal root C sf d s fullSize ε hε hs).simpleWitness R hR

/-- All global-existence spectral clauses refer to the literal live chain
and the unchanged HG2 probability family. -/
theorem same_family_literal_simpleWitness
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    (g : DerivedHG2Basins.GeometricSources (Ω := Ω) T A hA Λ ℓ D t terminal root C)
    (s : Fin t) (fullSize : (terminal s).val + 1 = ℓ)
    (ε : NNReal) (hε : 0 < ε) (hs : ε < d.window s 0) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
    Nonempty (SimpleSpectralWitness
      (DerivedHG2Conclusions.literalChain T A hA Λ ℓ D t terminal root C g ε) g.R
      (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε)) := by
  let : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
  have witness := same_family_simpleWitness T A hA Λ ℓ D t terminal root C sf d
    s fullSize g.R g.R_positive ε hε hs
  rwa [DerivedHG2Conclusions.actual_live_chain_eq_literal T A hA Λ ℓ D t terminal root C g ε] at witness

end ConditionedStochasticStabilityHyperbolic.Global.HG2FullSpectralConclusion
