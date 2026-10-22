module

public import ConditionedStochasticStabilityHyperbolic.Global.PaperStableGlobalConclusions
public import ConditionedStochasticStabilityHyperbolic.Spectral.CanonicalChainExt
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComparedLocalQuasiErgodic

/-! # Conditional HG2 conclusions from the constructed intermediate family

This is a derived application, not a claim that literal HG2 supplies the
extra strict-trapping or endpoint analytic source gates. The source interface
is constructed by the finite graph/filtration/analytic/collar pipeline.
-/
@[expose] public noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.PaperLiveObservableLimits
open AbsorbingMarkovChains LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry
open ActualFiltrationGrowth ActualPrefixBasicGeometry DerivedHG2Application DerivedHG2Basins
open ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic DerivedHG2Conclusions PaperStableBasin
variable {X I Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → CanonicalChain X) (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))
  (d : Families T A hA Λ ℓ D t terminal root C sf)
  (g : GeometricSources (Ω := Ω) T A hA Λ ℓ D t terminal root C)

omit [CompactSpace X] in
/-- Every actual stable basin has a single starting-state window for all
bounded measurable observables on the literal live state, without requiring
an ambient extension as part of the observable data. -/
theorem every_stable_basin_all_live_observables :
    ∀ j : Fin ℓ, ∃ s : Fin t, ∀ x ∈ stableBasin T (Λ (D.index j)),
      ∃ hx : x ∈ Aᶜ, ∃ δ : NNReal, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ →
        ∀ f : ↥(Aᶜ) → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
          Tendsto (MeasurableCanonical.pathAverage
            (literalChain T A hA Λ ℓ D t terminal root C g ε) f ⟨x, hx⟩) atTop
            (𝓝 (∫ y, f y ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)))) := by
  intro j
  obtain ⟨s, hs⟩ := PaperStableGlobalConclusions.every_stable_basin_literal_limit
    T A hA Λ ℓ D t terminal root C sf d g j
  refine ⟨s, ?_⟩
  intro x hx
  obtain ⟨hxLive, δ, hδ, hlimits⟩ := hs x hx
  refine ⟨hxLive, δ, hδ, ?_⟩
  intro ε hε hsmall f hf hb
  obtain ⟨B, hB⟩ := hb
  let f0 : X → ℝ := ComplexStrongFeller.zeroExtend Aᶜ f
  have hf0 : Measurable f0 := ComplexStrongFeller.measurable_zeroExtend Aᶜ hA.measurableSet.compl f hf
  have hb0 : ∃ B : ℝ, ∀ y, ‖f0 y‖ ≤ B :=
    ⟨max B 0, ComplexStrongFeller.norm_zeroExtend_le Aᶜ f (le_max_right B 0)
      (fun y => (hB y).trans (le_max_left B 0))⟩
  have hext : (fun y : ↥(Aᶜ) => f0 y.val) = f := by
    funext y
    exact ComplexStrongFeller.zeroExtend_coe Aᶜ f y
  have h := hlimits ε hε hsmall f0 hf0 hb0
  simpa only [hext] using h

omit [CompactSpace X] in
/-- On the original selected prefixes, one window works for all stable
starting states and all literal live-state bounded measurable observables. -/
theorem uniform_prefix_all_live_observables :
    ∃ δ : NNReal, 0 < δ ∧ ∀ j : Fin ℓ, ∃ s : Fin t,
      ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) 0,
        x ∈ stableBasin T (Λ (D.index j)) →
        ∃ hx : x ∈ Aᶜ, ∀ ε, 0 < ε → ε < δ →
          ∀ f : ↥(Aᶜ) → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
            Tendsto (MeasurableCanonical.pathAverage
              (literalChain T A hA Λ ℓ D t terminal root C g ε) f ⟨x, hx⟩) atTop
              (𝓝 (∫ y, f y ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)))) := by
  obtain ⟨δ, hδ, hlimits⟩ := uniform_prefix_literal_limits T A hA Λ ℓ D t terminal root C sf d g
  refine ⟨δ, hδ, ?_⟩
  intro j
  obtain ⟨s, hs⟩ := hlimits j
  refine ⟨s, ?_⟩
  intro x hxP hxStable
  obtain ⟨hxLive, hlim⟩ := hs x hxP (metric_approach_of_mem_stableBasin T (Λ (D.index j)) x hxStable)
  refine ⟨hxLive, ?_⟩
  intro ε hε hsmall f hf hb
  obtain ⟨B, hB⟩ := hb
  let f0 : X → ℝ := ComplexStrongFeller.zeroExtend Aᶜ f
  have hf0 : Measurable f0 := ComplexStrongFeller.measurable_zeroExtend Aᶜ hA.measurableSet.compl f hf
  have hb0 : ∃ B : ℝ, ∀ y, ‖f0 y‖ ≤ B :=
    ⟨max B 0, ComplexStrongFeller.norm_zeroExtend_le Aᶜ f (le_max_right B 0)
      (fun y => (hB y).trans (le_max_left B 0))⟩
  have hext : (fun y : ↥(Aᶜ) => f0 y.val) = f := by
    funext y
    exact ComplexStrongFeller.zeroExtend_coe Aᶜ f y
  have h := hlim ε hε hsmall f0 hf0 hb0
  simpa only [hext] using h

end ConditionedStochasticStabilityHyperbolic.Global.PaperLiveObservableLimits
