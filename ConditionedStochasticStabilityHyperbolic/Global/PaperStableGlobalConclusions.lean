module

public import ConditionedStochasticStabilityHyperbolic.Global.PaperStableBasin
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
namespace ConditionedStochasticStabilityHyperbolic.Global.PaperStableGlobalConclusions
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
/-- Every literal stable basin is assigned one selected live probability.
The starting-state window precedes the noise and every bounded measurable test. -/
theorem every_stable_basin_literal_limit :
    ∀ j : Fin ℓ, ∃ s : Fin t, ∀ x ∈ stableBasin T (Λ (D.index j)),
      ∃ hx : x ∈ Aᶜ, ∃ δ : NNReal, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ →
        ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
          Tendsto (MeasurableCanonical.pathAverage
            (literalChain T A hA Λ ℓ D t terminal root C g ε)
            (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩) atTop
            (𝓝 (∫ y, f y.val ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)))) := by
  intro j
  obtain ⟨s, hs⟩ := every_stable_start_literal_limit T A hA Λ ℓ D t terminal root C sf d g j
  exact ⟨s, fun x hx => hs x (metric_approach_of_mem_stableBasin T (Λ (D.index j)) x hx)⟩

end ConditionedStochasticStabilityHyperbolic.Global.PaperStableGlobalConclusions
