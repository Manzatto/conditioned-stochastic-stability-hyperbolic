module
public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Conclusions
public import ConditionedStochasticStabilityHyperbolic.Global.LiteralHG2Clauses

/-! Stable basin limits for the prescribed selected label, rather than an
existentially chosen label. The actual greedy interval theorem supplies the
finite path required here. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.PrescribedHG2Basins
open LeanShared ShiftedFiltrationGeometry ActualFiltrationGrowth ActualPrefixBasicGeometry
open DerivedHG2Application DerivedHG2Basins ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic
variable {X I Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
  (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))
  (d : Families T A hA Λ ℓ D t terminal root C sf)
  (g : GeometricSources (Ω := Ω) T A hA Λ ℓ D t terminal root C)
local instance prefixCompact (s : Fin t) (N : ℕ) :
    CompactSpace (actualPrefix T A Λ ℓ D (terminal s) N) :=
  isCompact_iff_compactSpace.mp (levels_positive_compact T A Λ ℓ N D
    ((terminal s).val + 1) (by omega) (by have _h := (terminal s).isLt; omega))

omit [CompactSpace X] in
theorem stable_limit (s : Fin t) (i : Fin ((terminal s).val + 1))
    (path : Relation.ReflTransGen (fun a b => g.edge (originalIndex a) (originalIndex b)) i (root s))
    (x : X) (approach : LiteralHG2Clauses.StableApproach T A Λ ℓ D (originalIndex i) x) :
    ∃ hx : x ∈ Aᶜ, ∃ δx : NNReal, 0 < δx ∧ ∀ ε, 0 < ε → ε < δx →
      ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
        Tendsto (MeasurableCanonical.pathAverage
          (DerivedHG2Conclusions.literalChain T A hA Λ ℓ D t terminal root C g ε)
          (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩) atTop
          (𝓝 (∫ y, f y.val ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)))) := by
  have live := DerivedHG2Conclusions.stable_start_live T A hA Λ ℓ D t terminal root C g
    (originalIndex i) x approach
  have hinv := (actual_prefix_basic_properties T A hA Λ ℓ 0 D g.separation
    ((terminal s).val + 1) (by have _h := (terminal s).isLt; omega) i).2.1
  obtain ⟨N, _hN, hx, _⟩ := ActualStablePrefixEntry.exists_actual_shifted_prefix_for_stable_start
    T A hA g.strict_trapping Λ ℓ D g.separation (originalIndex i)
    ((terminal s).val + 1) i.isLt (by have _h := (terminal s).isLt; omega) hinv x approach
  refine ⟨live, min (d.window s 0) (d.window s N),
    lt_min (d.window_positive s 0) (d.window_positive s N), ?_⟩
  intro ε hε hsmall f hf hb
  rw [DerivedHG2Conclusions.literal_pathAverage_eq_ambient T A hA Λ ℓ D t terminal root C sf d g ε hε f hf hb]
  exact stable_limit_to_original_live_probability T A hA Λ ℓ D t terminal root C sf d g
    s N ε hε (hsmall.trans_le (min_le_left _ _)) (hsmall.trans_le (min_le_right _ _))
    i path ⟨x, interior_subset hx⟩ approach f hf hb

omit [CompactSpace X] in
theorem uniform_prefix_limits :
    ∃ δ : NNReal, 0 < δ ∧ ∀ s : Fin t, ∀ i : Fin ((terminal s).val + 1),
      Relation.ReflTransGen (fun a b => g.edge (originalIndex a) (originalIndex b)) i (root s) →
      ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) 0,
        LiteralHG2Clauses.StableApproach T A Λ ℓ D (originalIndex i) x →
        ∃ hx : x ∈ Aᶜ, ∀ ε, 0 < ε → ε < δ → ∀ f : X → ℝ, Measurable f →
          (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
          Tendsto (MeasurableCanonical.pathAverage
            (DerivedHG2Conclusions.literalChain T A hA Λ ℓ D t terminal root C g ε)
            (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩) atTop
            (𝓝 (∫ y, f y.val ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)))) := by
  obtain ⟨δ, positive, bounds⟩ := exists_common_base_window T A hA Λ ℓ D t terminal root C sf d
  refine ⟨δ, positive, ?_⟩
  intro s i path x hx approach
  have live := DerivedHG2Conclusions.stable_start_live T A hA Λ ℓ D t terminal root C g
    (originalIndex i) x approach
  refine ⟨live, ?_⟩
  intro ε hε small f hf hb
  rw [DerivedHG2Conclusions.literal_pathAverage_eq_ambient T A hA Λ ℓ D t terminal root C sf d g ε hε f hf hb]
  exact stable_limit_to_original_live_probability T A hA Λ ℓ D t terminal root C sf d g
    s 0 ε hε (small.trans_le (bounds s)) (small.trans_le (bounds s))
    i path ⟨x, hx⟩ approach f hf hb
end ConditionedStochasticStabilityHyperbolic.Global.PrescribedHG2Basins
