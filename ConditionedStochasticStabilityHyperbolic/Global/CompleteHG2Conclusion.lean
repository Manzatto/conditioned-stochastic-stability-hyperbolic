module
public import ConditionedStochasticStabilityHyperbolic.Global.LabelledHG2Clauses
public import ConditionedStochasticStabilityHyperbolic.Global.HG2FullSpectralConclusion

/-! One common window retains every HG2 clause, its exact prescribed group
labels, and full leading spectral simplicity for the unchanged first QEM. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.CompleteHG2Conclusion
open LeanShared ShiftedFiltrationGeometry DerivedHG2Application DerivedHG2Basins
variable {X I Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
  (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))
  (d : Families T A hA Λ ℓ D t terminal root C sf)
  (g : GeometricSources (Ω := Ω) T A hA Λ ℓ D t terminal root C)

theorem conclude {δ₀ : NNReal} (positive : 0 < δ₀)
    (clauses : DerivedHG2Conclusions.ConclusionClauses T A hA Λ ℓ D t terminal root C sf d g δ₀)
    (reach : ∀ s : Fin t, ∀ i : Fin ((terminal s).val + 1), (root s).val ≤ i.val →
      Relation.ReflTransGen (fun a b => g.edge (originalIndex a) (originalIndex b)) i (root s))
    (first : Fin t) (full : (terminal first).val + 1 = ℓ) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
    ∃ δ : NNReal, 0 < δ ∧ δ ≤ δ₀ ∧ δ ≤ d.window first 0 ∧
      LiteralHG2Clauses.Clauses T A Λ ℓ D t terminal root
        (DerivedHG2Conclusions.literalChain T A hA Λ ℓ D t terminal root C g) g.maps
        (liveLaw T A hA Λ ℓ D t terminal root C sf d) d.equilibrium δ ∧
      LabelledHG2Clauses.Clauses T A Λ ℓ D t terminal root
        (DerivedHG2Conclusions.literalChain T A hA Λ ℓ D t terminal root C g)
        (liveLaw T A hA Λ ℓ D t terminal root C sf d) δ ∧
      ∀ ε, 0 < ε → ε < δ → Nonempty (Paper.LocalConclusions.SimpleSpectralWitness
        (DerivedHG2Conclusions.literalChain T A hA Λ ℓ D t terminal root C g ε) g.R
        (liveLaw T A hA Λ ℓ D t terminal root C sf d first ε)) := by
  let : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp hA.isClosed_compl.isCompact
  obtain ⟨δlabel, positiveLabel, labelled⟩ := LabelledHG2Clauses.of_derived hA C sf d g reach
  let δ := min δ₀ (min δlabel (d.window first 0))
  have hw : 0 < min δlabel (d.window first 0) := lt_min positiveLabel (d.window_positive first 0)
  have actual := LiteralHG2Clauses.of_derived C sf d g clauses
  have nine := actual.transfer_window hw (fun _ _ => rfl) (fun _ _ => rfl)
  have fixedLabel := labelled.transfer_window (lt_min positive (d.window_positive first 0)) (fun _ _ => rfl)
  refine ⟨δ, lt_min positive hw, min_le_left _ _, (min_le_right _ _).trans (min_le_right _ _), nine, ?_, ?_⟩
  · simpa only [δ, min_left_comm] using fixedLabel
  · intro ε hε small
    exact HG2FullSpectralConclusion.same_family_literal_simpleWitness T A hA Λ ℓ D t terminal root C sf d g
      first full ε hε (small.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
end ConditionedStochasticStabilityHyperbolic.Global.CompleteHG2Conclusion
