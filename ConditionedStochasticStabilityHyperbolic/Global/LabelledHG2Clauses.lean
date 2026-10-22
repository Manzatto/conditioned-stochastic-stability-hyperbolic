module
public import ConditionedStochasticStabilityHyperbolic.Global.PrescribedHG2Basins

/-! Exact prescribed-group basin conclusions on the literal process. The
interval [root s,terminal s] is precisely the manuscript interval, by the
checked adjacent-root/prefix-size identities. This output predicate survives
exact agreement of the original process on a positive noise window. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.LabelledHG2Clauses
open LeanShared ShiftedFiltrationGeometry DerivedHG2Application DerivedHG2Basins
variable {X I : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → AbsorbingMarkovChains.CanonicalChain ↥(Aᶜ))
  (ν : Fin t → NNReal → ProbabilityMeasure ↥(Aᶜ))

structure Clauses (δ : NNReal) : Prop where
  uniform_prefix : ∀ s : Fin t, ∀ i : Fin ((terminal s).val + 1), (root s).val ≤ i.val →
    ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) 0,
      LiteralHG2Clauses.StableApproach T A Λ ℓ D (originalIndex i) x →
      ∃ hx : x ∈ Aᶜ, ∀ ε, 0 < ε → ε < δ → ∀ f : X → ℝ, Measurable f →
        (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
        Tendsto (MeasurableCanonical.pathAverage (C ε) (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩)
          atTop (𝓝 (∫ y, f y.val ∂(ν s ε : Measure ↥(Aᶜ))))
  all_stable : ∀ s : Fin t, ∀ i : Fin ((terminal s).val + 1), (root s).val ≤ i.val →
    ∀ x : X, LiteralHG2Clauses.StableApproach T A Λ ℓ D (originalIndex i) x →
      ∃ hx : x ∈ Aᶜ, ∃ δx : NNReal, 0 < δx ∧ ∀ ε, 0 < ε → ε < δx →
      ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
        Tendsto (MeasurableCanonical.pathAverage (C ε) (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩)
          atTop (𝓝 (∫ y, f y.val ∂(ν s ε : Measure ↥(Aᶜ))))

variable {T A Λ ℓ D t terminal root C ν}
omit [CompactSpace X] [BorelSpace X] in
theorem Clauses.transfer_window
    {C' : NNReal → AbsorbingMarkovChains.CanonicalChain ↥(Aᶜ)} {δ window : NNReal}
    (h : Clauses T A Λ ℓ D t terminal root C' ν δ) (positive : 0 < window)
    (same : ∀ ε, ε ≤ window → C' ε = C ε) :
    Clauses T A Λ ℓ D t terminal root C ν (min δ window) := by
  constructor
  · intro s i lower x hx approach
    obtain ⟨live, limits⟩ := h.uniform_prefix s i lower x hx approach
    refine ⟨live, ?_⟩
    intro ε he small f hf hb
    rw [← same ε (small.trans_le (min_le_right _ _)).le]
    exact limits ε he (small.trans_le (min_le_left _ _)) f hf hb
  · intro s i lower x approach
    obtain ⟨live, δx, hδx, limits⟩ := h.all_stable s i lower x approach
    refine ⟨live, min δx window, lt_min hδx positive, ?_⟩
    intro ε he small f hf hb
    rw [← same ε (small.trans_le (min_le_right _ _)).le]
    exact limits ε he (small.trans_le (min_le_left _ _)) f hf hb

omit [CompactSpace X] in
theorem of_derived
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    (hA : IsOpen A) (B : NNReal → AbsorbingMarkovChains.CanonicalChain X)
    (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (B ε))
    (d : Families T A hA Λ ℓ D t terminal root B sf)
    (g : GeometricSources (Ω := Ω) T A hA Λ ℓ D t terminal root B)
    (reach : ∀ s : Fin t, ∀ i : Fin ((terminal s).val + 1), (root s).val ≤ i.val →
      Relation.ReflTransGen (fun a b => g.edge (originalIndex a) (originalIndex b)) i (root s)) :
    ∃ δ : NNReal, 0 < δ ∧ Clauses T A Λ ℓ D t terminal root
      (DerivedHG2Conclusions.literalChain T A hA Λ ℓ D t terminal root B g)
      (liveLaw T A hA Λ ℓ D t terminal root B sf d) δ := by
  obtain ⟨δ, positive, limits⟩ := PrescribedHG2Basins.uniform_prefix_limits
    T A hA Λ ℓ D t terminal root B sf d g
  refine ⟨δ, positive, ?_, ?_⟩
  · intro s i lower
    exact limits s i (reach s i lower)
  · intro s i lower x approach
    exact PrescribedHG2Basins.stable_limit T A hA Λ ℓ D t terminal root B sf d g
      s i (reach s i lower) x approach
end ConditionedStochasticStabilityHyperbolic.Global.LabelledHG2Clauses
