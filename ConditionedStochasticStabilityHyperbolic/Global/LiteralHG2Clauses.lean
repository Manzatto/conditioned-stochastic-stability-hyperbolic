module

public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Conclusions

/-! The global-global conclusions as properties of the original literal
process and probability family, independent of an all-positive spectral
interface. They are invariant under exact agreement on a positive window. -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.LiteralHG2Clauses
open AbsorbingMarkovChains LeanShared ShiftedFiltrationGeometry
open DerivedHG2Application DerivedHG2Basins
variable {X I Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Ω]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → CanonicalChain ↥(Aᶜ)) (maps : NNReal → X × Ω → X)
  (ν : Fin t → NNReal → ProbabilityMeasure ↥(Aᶜ))
  (equilibrium : Fin t → ProbabilityMeasure ↥(Aᶜ))

abbrev StableApproach (j : Fin ℓ) (x : X) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index j), dist ((T : X → X)^[n + 1] x) y < r

structure Clauses (δ : NNReal) : Prop where
  number_selected : 0 < t ∧ t ≤ ℓ
  quasiErgodic : ∀ ε, 0 < ε → ε < δ → ∀ s : Fin t, (C ε).IsQuasiErgodic (ν s ε)
  support : ∀ ε, 0 < ε → ε < δ → ∀ s : Fin t,
    {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (originalIndex (root s)))} ⊆ (ν s ε : Measure ↥(Aᶜ)).support
  uniqueness : ∀ ε, 0 < ε → ε < δ → ∀ s : Fin t, ∀ η : Measure ↥(Aᶜ),
    (C ε).IsQuasiErgodic η →
    {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (originalIndex (root s)))} ⊆ η.support →
    η = (ν s ε : Measure ↥(Aᶜ))
  distinct : ∀ ε, 0 < ε → ε < δ → Function.Injective (fun s : Fin t => ν s ε)
  uniform_prefix : ∀ j : Fin ℓ, ∃ s : Fin t,
    ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) 0, StableApproach T A Λ ℓ D j x →
    ∃ hx : x ∈ Aᶜ, ∀ ε, 0 < ε → ε < δ → ∀ f : X → ℝ, Measurable f →
      (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
      Tendsto (MeasurableCanonical.pathAverage (C ε) (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩)
        atTop (𝓝 (∫ y, f y.val ∂(ν s ε : Measure ↥(Aᶜ))))
  all_stable : ∀ j : Fin ℓ, ∃ s : Fin t, ∀ x : X, StableApproach T A Λ ℓ D j x →
    ∃ hx : x ∈ Aᶜ, ∃ δx : NNReal, 0 < δx ∧ ∀ ε, 0 < ε → ε < δx →
    ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
      Tendsto (MeasurableCanonical.pathAverage (C ε) (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩)
        atTop (𝓝 (∫ y, f y.val ∂(ν s ε : Measure ↥(Aᶜ))))
  equilibrium_limit : ∀ s : Fin t, Tendsto (ν s) (𝓝[>] 0) (𝓝 (equilibrium s))
  absorption : ∀ x : X, (∃ n : ℕ, (T : X → X)^[n] x ∈ A) →
    ∃ N : ℕ, 0 < N ∧ ∃ δx : NNReal, 0 < δx ∧ ∀ ε, 0 < ε → ε < δx → ∀ controls : ℕ → Ω,
    GlobalAbsorptionEveryControl.positiveEntranceTime
      (nonautonomousOrbit (fun n z => maps ε (z, controls n)) x) A ≤ (N : WithTop ℕ)

variable {T A hA Λ ℓ D t terminal root C maps ν equilibrium}

omit [CompactSpace X] [MeasurableSpace Ω] in
theorem Clauses.transfer_window {C' : NNReal → CanonicalChain ↥(Aᶜ)}
    {maps' : NNReal → X × Ω → X} {δ window : NNReal}
    (h : Clauses T A Λ ℓ D t terminal root C' maps' ν equilibrium δ)
    (hw : 0 < window)
    (chains_eq : ∀ ε, ε ≤ window → C' ε = C ε)
    (maps_eq : ∀ ε, ε ≤ window → maps' ε = maps ε) :
    Clauses T A Λ ℓ D t terminal root C maps ν equilibrium (min δ window) := by
  refine {
    number_selected := h.number_selected
    quasiErgodic := ?_
    support := ?_
    uniqueness := ?_
    distinct := ?_
    uniform_prefix := ?_
    all_stable := ?_
    equilibrium_limit := h.equilibrium_limit
    absorption := ?_ }
  · intro ε hε hs s
    rw [← chains_eq ε (hs.trans_le (min_le_right _ _)).le]
    exact h.quasiErgodic ε hε (hs.trans_le (min_le_left _ _)) s
  · intro ε hε hs s
    exact h.support ε hε (hs.trans_le (min_le_left _ _)) s
  · intro ε hε hs s η hη hsup
    apply h.uniqueness ε hε (hs.trans_le (min_le_left _ _)) s η _ hsup
    rwa [chains_eq ε (hs.trans_le (min_le_right _ _)).le]
  · intro ε hε hs
    exact h.distinct ε hε (hs.trans_le (min_le_left _ _))
  · intro j
    obtain ⟨s, hs⟩ := h.uniform_prefix j
    refine ⟨s, ?_⟩
    intro x hx ha
    obtain ⟨hlive, hh⟩ := hs x hx ha
    refine ⟨hlive, ?_⟩
    intro ε hε hsmall f hf hb
    rw [← chains_eq ε (hsmall.trans_le (min_le_right _ _)).le]
    exact hh ε hε (hsmall.trans_le (min_le_left _ _)) f hf hb
  · intro j
    obtain ⟨s, hs⟩ := h.all_stable j
    refine ⟨s, ?_⟩
    intro x ha
    obtain ⟨hlive, δx, hδx, hh⟩ := hs x ha
    refine ⟨hlive, min δx window, lt_min hδx hw, ?_⟩
    intro ε hε hsmall f hf hb
    rw [← chains_eq ε (hsmall.trans_le (min_le_right _ _)).le]
    exact hh ε hε (hsmall.trans_le (min_le_left _ _)) f hf hb
  · intro x hx
    obtain ⟨N, hN, δx, hδx, hh⟩ := h.absorption x hx
    refine ⟨N, hN, min δx window, lt_min hδx hw, ?_⟩
    intro ε hε hsmall controls
    rw [← maps_eq ε (hsmall.trans_le (min_le_right _ _)).le]
    exact hh ε hε (hsmall.trans_le (min_le_left _ _)) controls

variable [TopologicalSpace Ω]

omit [CompactSpace X] in
theorem of_derived
    (B : NNReal → CanonicalChain X) (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (B ε))
    (d : Families T A hA Λ ℓ D t terminal root B sf)
    (g : GeometricSources (Ω := Ω) T A hA Λ ℓ D t terminal root B)
    {δ : NNReal} (h : DerivedHG2Conclusions.ConclusionClauses
      T A hA Λ ℓ D t terminal root B sf d g δ) :
    Clauses T A Λ ℓ D t terminal root
      (DerivedHG2Conclusions.literalChain T A hA Λ ℓ D t terminal root B g) g.maps
      (liveLaw T A hA Λ ℓ D t terminal root B sf d) d.equilibrium δ :=
  ⟨h.number_selected, h.quasiErgodic, h.support, h.uniqueness, h.distinct,
    h.uniform_prefix, h.all_stable, h.equilibrium_limit, h.absorption⟩

end ConditionedStochasticStabilityHyperbolic.Global.LiteralHG2Clauses
