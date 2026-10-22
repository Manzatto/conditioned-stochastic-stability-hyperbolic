module

public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Basins
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
namespace ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Conclusions
open AbsorbingMarkovChains LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry
open ActualFiltrationGrowth ActualPrefixBasicGeometry DerivedHG2Application DerivedHG2Basins
open ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic
variable {X I Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → CanonicalChain X) (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))
  (d : Families T A hA Λ ℓ D t terminal root C sf)
  (g : GeometricSources (Ω := Ω) T A hA Λ ℓ D t terminal root C)

local instance prefixCompact (s : Fin t) (N : ℕ) : CompactSpace (actualPrefix T A Λ ℓ D (terminal s) N) :=
  isCompact_iff_compactSpace.mp (levels_positive_compact T A Λ ℓ N D ((terminal s).val + 1) (by omega) (by have h := (terminal s).isLt; omega))

/-- The manuscript's exact weighted chain with live state Aᶜ. -/
def literalChain (ε : NNReal) : CanonicalChain ↥(Aᶜ) := by
  let : IsProbabilityMeasure (g.noise ε) := g.probability ε
  exact RestrictedNoise.chain (g.noise ε) (g.maps ε) (g.measurable ε) Aᶜ hA.measurableSet.compl
    (fun x : ↥(Aᶜ) => Real.exp (g.potential x.val))
    ((Real.measurable_exp.comp g.potential_measurable).comp measurable_subtype_coe)
    g.R g.R_positive (fun x => g.weight_bound x.val)

omit [CompactSpace X] in
theorem actual_live_chain_eq_literal (ε : NNReal) :
    chain (C ε) Aᶜ hA.measurableSet.compl = literalChain T A hA Λ ℓ D t terminal root C g ε := by
  let : IsProbabilityMeasure (g.noise ε) := g.probability ε
  have hc := canonicalChain_eq_of_killedTransition_eq _ _ (g.actual_model ε)
  rw [hc]
  exact (LiteralNoiseLiveChain.actual_live_chain_eq_restriction (g.noise ε) (g.maps ε)
    (g.measurable ε) A hA.measurableSet g.potential g.potential_measurable g.R
    g.R_positive g.weight_bound).symm

omit [CompactSpace X] in
theorem selected_literal_QEM (s : Fin t) (ε : NNReal) (hε : 0 < ε)
    (hs : ε < d.window s 0) :
    (literalChain T A hA Λ ℓ D t terminal root C g ε).IsQuasiErgodic
      (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε) := by
  rw [← actual_live_chain_eq_literal T A hA Λ ℓ D t terminal root C g ε]
  exact liveProbability_isQuasiErgodic T A hA Λ ℓ D t terminal root C sf d s ε hε hs

include d in
omit [CompactSpace X] in
theorem number_selected_le_number_retained : t ≤ ℓ := by
  have hinj : Function.Injective (fun s : Fin t => (originalIndex (root s) : Fin ℓ)) := by
    intro s q he
    have hv := congrArg Fin.val he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hsq | hqs
    · have hb := d.root_above_later s q hsq
      have hh := (root q).isLt
      change (root s).val = (root q).val at hv
      omega
    · have hb := d.root_above_later q s hqs
      have hh := (root s).isLt
      change (root s).val = (root q).val at hv
      omega
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

include g in
omit [CompactSpace X] in
theorem number_selected_positive (hℓ : 0 < ℓ) : 0 < t := by
  obtain ⟨s, _⟩ := g.assignment ⟨0, hℓ⟩
  exact Nat.zero_lt_of_lt s.isLt

omit [CompactSpace X] in
/-- Literal live QEM existence, distinctness and weak equilibrium convergence
hold on a single window before every selected block. -/
theorem exists_common_window_literal_QEMs_distinct_weak :
    ∃ δ : NNReal, 0 < δ ∧
      (∀ ε, 0 < ε → ε < δ → ∀ s : Fin t,
        (literalChain T A hA Λ ℓ D t terminal root C g ε).IsQuasiErgodic
          (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε)) ∧
      (∀ ε, 0 < ε → ε < δ → Function.Injective
        (fun s : Fin t => liveLaw T A hA Λ ℓ D t terminal root C sf d s ε)) ∧
      ∀ s : Fin t, Tendsto (liveLaw T A hA Λ ℓ D t terminal root C sf d s)
        (𝓝[>] 0) (𝓝 (d.equilibrium s)) := by
  obtain ⟨δ, hδ, hwindow⟩ := exists_common_base_window T A hA Λ ℓ D t terminal root C sf d
  refine ⟨δ, hδ, ?_, ?_, liveLaw_tendsto_equilibrium T A hA Λ ℓ D t terminal root C sf d⟩
  · intro ε hε hsmall s
    exact selected_literal_QEM T A hA Λ ℓ D t terminal root C sf d g s ε hε (hsmall.trans_le (hwindow s))
  · intro ε hε hsmall s q he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hsq | hqs
    · exact liveLaw_pairwise_distinct T A hA Λ ℓ D t terminal root C sf d ε hε
        (fun s => hsmall.trans_le (hwindow s)) hsq he
    · exact liveLaw_pairwise_distinct T A hA Λ ℓ D t terminal root C sf d ε hε
        (fun s => hsmall.trans_le (hwindow s)) hqs he.symm

include d in
omit [CompactSpace X] in
theorem literal_pathAverage_eq_ambient
    (ε : NNReal) (hε : 0 < ε) (f : X → ℝ) (hf : Measurable f)
    (hb : ∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) (x : ↥(Aᶜ)) :
    MeasurableCanonical.pathAverage (literalChain T A hA Λ ℓ D t terminal root C g ε)
      (fun y : ↥(Aᶜ) => f y.val) x = MeasurableCanonical.pathAverage (C ε) f x.val := by
  rw [← actual_live_chain_eq_literal T A hA Λ ℓ D t terminal root C g ε]
  obtain ⟨B, hB⟩ := hb
  funext n
  exact PrefixCorrespondence.conditioned_average_eq (C ε) Aᶜ hA.measurableSet.compl
    (by intro z hz; simpa only [compl_compl] using d.zero_absorbing ε hε z)
    f hf (max B 0) (le_max_right B 0) (fun y => (hB y).trans (le_max_left B 0)) n x

include g in
omit [CompactSpace X] in
theorem stable_start_live (j : Fin ℓ) (x : X)
    (happroach : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index j),
      dist ((T : X → X)^[n + 1] x) y < r) : x ∈ Aᶜ := by
  have hinv : MapsTo T (Λ (D.index j)) (Λ (D.index j)) := by
    rw [← literal_core T A Λ ℓ 0 D j]
    exact mapsTo_isolatedCore T _
  have happ := ActualBasinGeometry.approaches_of_metric T (Λ (D.index j))
    (StableShiftEntry.basic_set_compact T A hA Λ ℓ 0 D j) x (by
      intro r hr
      obtain ⟨n, y, hy, hd⟩ := happroach r hr
      exact ⟨n + 1, y, hy, hd⟩)
  exact interior_subset (ActualBasinGeometry.retained_stable_point_live_interior
    T A (Λ (D.index j)) g.strict_trapping (g.separation _) hinv x happ)

include g in
omit [CompactSpace X] in
/-- Global-global(ii) with the exact literal live chain and δ(x) chosen
before ε and every bounded measurable observable. -/
theorem every_stable_start_literal_limit :
    ∀ j : Fin ℓ, ∃ s : Fin t, ∀ x : X,
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index j),
        dist ((T : X → X)^[n + 1] x) y < r) →
      ∃ hx : x ∈ Aᶜ, ∃ δ : NNReal, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ →
        ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
          Tendsto (MeasurableCanonical.pathAverage
            (literalChain T A hA Λ ℓ D t terminal root C g ε)
            (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩) atTop
            (𝓝 (∫ y, f y.val ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)))) := by
  intro j
  obtain ⟨s, hlimits⟩ := every_retained_stable_start_has_selected_limit T A hA Λ ℓ D t terminal root C sf d g j
  refine ⟨s, ?_⟩
  intro x happ
  have hx := stable_start_live T A hA Λ ℓ D t terminal root C g j x happ
  obtain ⟨δ, hδ, hlim⟩ := hlimits x happ
  refine ⟨hx, δ, hδ, ?_⟩
  intro ε hε hsmall f hf hb
  rw [literal_pathAverage_eq_ambient T A hA Λ ℓ D t terminal root C sf d g ε hε f hf hb ⟨x, hx⟩]
  exact hlim ε hε hsmall f hf hb

include g in
omit [CompactSpace X] in
/-- Global-global(i) uses one window before all selected basins, prefix
starting states, noise sizes and bounded measurable observables. -/
theorem uniform_prefix_literal_limits :
    ∃ δ : NNReal, 0 < δ ∧ ∀ j : Fin ℓ, ∃ s : Fin t,
      ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) 0,
        (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index j),
          dist ((T : X → X)^[n + 1] x) y < r) →
        ∃ hx : x ∈ Aᶜ, ∀ ε, 0 < ε → ε < δ → ∀ f : X → ℝ, Measurable f →
          (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
            Tendsto (MeasurableCanonical.pathAverage
              (literalChain T A hA Λ ℓ D t terminal root C g ε)
              (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩) atTop
              (𝓝 (∫ y, f y.val ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)))) := by
  obtain ⟨δ, hδ, hlimits⟩ := exists_uniform_original_prefix_basin_window T A hA Λ ℓ D t terminal root C sf d g
  refine ⟨δ, hδ, ?_⟩
  intro j
  obtain ⟨s, hs⟩ := hlimits j
  refine ⟨s, ?_⟩
  intro x hx happ
  have hxl := stable_start_live T A hA Λ ℓ D t terminal root C g j x happ
  refine ⟨hxl, ?_⟩
  intro ε hε hsmall f hf hb
  rw [literal_pathAverage_eq_ambient T A hA Λ ℓ D t terminal root C sf d g ε hε f hf hb ⟨x, hxl⟩]
  exact hs x hx happ ε hε hsmall f hf hb

include g in
/-- Global-global(iv) for every control sequence, including time-zero
initial entrance, in the same actual positive-noise family. -/
theorem every_control_absorption
    (c : ℝ) (hc : 0 ≤ c)
    (hnoise : ∀ ε : NNReal, 0 < ε → ∀ z ω,
      dist (g.maps ε (z, ω)) (T z) ≤ c * (ε : ℝ)) :
    ∀ x : X, (∃ n : ℕ, (T : X → X)^[n] x ∈ A) →
      ∃ N : ℕ, 0 < N ∧ ∃ δ : NNReal, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ → ∀ controls : ℕ → Ω,
        GlobalAbsorptionEveryControl.positiveEntranceTime
          (LeanShared.nonautonomousOrbit (fun n z => g.maps ε (z, controls n)) x) A ≤ (N : WithTop ℕ) := by
  intro x hx
  obtain ⟨N, hN, δ, hδ, hall⟩ := GlobalAbsorptionEveryControl.exists_uniform_every_control_absorption
    T (CompactSpace.uniformContinuous_of_continuous T.continuous) A hA D.absorbing_forward x hx
    (fun a => g.maps a.toNNReal) hc (by
      intro a ha z ω
      simpa [Real.toNNReal_of_nonneg ha.le] using hnoise a.toNNReal (Real.toNNReal_pos.mpr ha) z ω)
  refine ⟨N, hN, δ.toNNReal, Real.toNNReal_pos.mpr hδ, ?_⟩
  intro ε hε hsmall controls
  have hlt : (ε : ℝ) < δ := by
    have hh : (ε : ℝ) < (δ.toNNReal : ℝ) := NNReal.coe_lt_coe.mpr hsmall
    simpa [Real.toNNReal_of_nonneg hδ.le] using hh
  have h := hall (ε : ℝ) (NNReal.coe_pos.mpr hε) hlt controls
  simpa only [Real.toNNReal_coe] using h

omit [CompactSpace X] in
theorem selected_core_support (s : Fin t) (ε : NNReal) (hε : 0 < ε) (hs : ε < d.window s 0) :
    {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (originalIndex (root s)))} ⊆
      (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)).support := by
  intro x hx
  apply ComparedLocalQuasiErgodic.mem_support_of_mem_support_map Aᶜ _ x
  have hm := congrArg (fun ν : ProbabilityMeasure X => (ν : Measure X))
    (liveLaw_map T A hA Λ ℓ D t terminal root C sf d s ε)
  change (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)).map Subtype.val =
    (d.closedProduct s ε).map Subtype.val at hm
  rw [hm]
  have h := d.core_support s 0 ε hε hs hx
  rw [d.base_product_identity s ε hε hs] at h
  exact h

omit [CompactSpace X] in
theorem selected_literal_QEM_unique_with_core_support
    (s : Fin t) (ε : NNReal) (hε : 0 < ε) (hs : ε < d.window s 0)
    (η : Measure ↥(Aᶜ))
    (hq : (literalChain T A hA Λ ℓ D t terminal root C g ε).IsQuasiErgodic η)
    (hη : {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (originalIndex (root s)))} ⊆ η.support) :
    η = (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)) := by
  rw [← actual_live_chain_eq_literal T A hA Λ ℓ D t terminal root C g ε] at hq
  have hfull := PrefixQuasiErgodic.full_process_isQuasiErgodic_of_prefix (C ε) Aᶜ hA.measurableSet.compl
    (by intro x hx; simpa only [compl_compl] using d.zero_absorbing ε hε x) η hq
  obtain ⟨p, hp⟩ := d.core_nonempty s
  have hpLive : p ∈ Aᶜ := interior_subset (g.separation _ hp)
  have hpη : p ∈ (η.map Subtype.val).support :=
    LayerProductCorrespondence.subtype_support_maps_into η (hη (show (⟨p, hpLive⟩ : ↥(Aᶜ)).val ∈ _ from hp))
  have hpi := (actual_prefix_basic_properties T A hA Λ ℓ 0 D g.separation
    ((terminal s).val + 1) (by have h := (terminal s).isLt; omega) (root s)).2.2.2 hp
  let p₀ : actualPrefix T A Λ ℓ D (terminal s) 0 := ⟨p, interior_subset hpi.1⟩
  have he := PrefixUniqueness.full_QEM_eq_prefix_product_of_support (C ε) (sf ε hε)
    (actualPrefix T A Λ ℓ D (terminal s) 0)
    (ambient_levels_measurable T A hA Λ ℓ 0 D ((terminal s).val + 1))
    (d.invariant s 0 ε hε hs) (d.data s 0 ε hε hs) _ hfull p₀ hpη hpi.1
    (d.core_positive s 0 ε hε hs p₀ hp)
  apply (MeasurableEmbedding.subtype_coe hA.measurableSet.compl).map_injective
  rw [he, d.base_product_identity s ε hε hs]
  exact (congrArg (fun ν : ProbabilityMeasure X => (ν : Measure X))
    (liveLaw_map T A hA Λ ℓ D t terminal root C sf d s ε)).symm

abbrev AllStableLimits  : Prop :=
  ∀ j : Fin ℓ, ∃ s : Fin t, ∀ x : X,
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index j),
        dist ((T : X → X)^[n + 1] x) y < r) →
      ∃ hx : x ∈ Aᶜ, ∃ δ : NNReal, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ →
        ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
          Tendsto (MeasurableCanonical.pathAverage
            (literalChain T A hA Λ ℓ D t terminal root C g ε)
            (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩) atTop
            (𝓝 (∫ y, f y.val ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ))))

abbrev UniformPrefixLimits (δ : NNReal) : Prop :=
  ∀ j : Fin ℓ, ∃ s : Fin t,
      ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) 0,
        (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index j),
          dist ((T : X → X)^[n + 1] x) y < r) →
        ∃ hx : x ∈ Aᶜ, ∀ ε, 0 < ε → ε < δ → ∀ f : X → ℝ, Measurable f →
          (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
            Tendsto (MeasurableCanonical.pathAverage
              (literalChain T A hA Λ ℓ D t terminal root C g ε)
              (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩) atTop
              (𝓝 (∫ y, f y.val ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ))))

abbrev EveryControlAbsorption  : Prop :=
  ∀ x : X, (∃ n : ℕ, (T : X → X)^[n] x ∈ A) →
      ∃ N : ℕ, 0 < N ∧ ∃ δ : NNReal, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ → ∀ controls : ℕ → Ω,
        GlobalAbsorptionEveryControl.positiveEntranceTime
          (LeanShared.nonautonomousOrbit (fun n z => g.maps ε (z, controls n)) x) A ≤ (N : WithTop ℕ)

/-- All HG2 conclusions, on one common original-prefix window. The sources
remain explicitly derived data; this predicate does not assert literal HG2
implies the extra trapping and endpoint analytic gates. -/
structure ConclusionClauses (δ : NNReal) : Prop where
  number_selected : 0 < t ∧ t ≤ ℓ
  quasiErgodic : ∀ ε, 0 < ε → ε < δ → ∀ s : Fin t,
    (literalChain T A hA Λ ℓ D t terminal root C g ε).IsQuasiErgodic
      (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε)
  support : ∀ ε, 0 < ε → ε < δ → ∀ s : Fin t,
    {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (originalIndex (root s)))} ⊆
      (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)).support
  uniqueness : ∀ ε, 0 < ε → ε < δ → ∀ s : Fin t, ∀ η : Measure ↥(Aᶜ),
    (literalChain T A hA Λ ℓ D t terminal root C g ε).IsQuasiErgodic η →
    {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (originalIndex (root s)))} ⊆ η.support →
    η = (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ))
  distinct : ∀ ε, 0 < ε → ε < δ → Function.Injective
    (fun s : Fin t => liveLaw T A hA Λ ℓ D t terminal root C sf d s ε)
  uniform_prefix : UniformPrefixLimits T A hA Λ ℓ D t terminal root C sf d g δ
  all_stable : AllStableLimits T A hA Λ ℓ D t terminal root C sf d g
  equilibrium_limit : ∀ s : Fin t, Tendsto (liveLaw T A hA Λ ℓ D t terminal root C sf d s)
    (𝓝[>] 0) (𝓝 (d.equilibrium s))
  absorption : EveryControlAbsorption T A hA Λ ℓ D t terminal root C g

/-- The named conditional global-global application. All probability,
uniqueness, stable-basin and weak-limit conclusions are derived here. -/
theorem conditional_global_global
    (hℓ : 0 < ℓ) (c : ℝ) (hc : 0 ≤ c)
    (hnoise : ∀ ε : NNReal, 0 < ε → ∀ z ω,
      dist (g.maps ε (z, ω)) (T z) ≤ c * (ε : ℝ)) :
    ∃ δ : NNReal, 0 < δ ∧ ConclusionClauses T A hA Λ ℓ D t terminal root C sf d g δ := by
  obtain ⟨δB, hδB, hbase⟩ := exists_common_base_window T A hA Λ ℓ D t terminal root C sf d
  obtain ⟨δP, hδP, hprefix⟩ := uniform_prefix_literal_limits T A hA Λ ℓ D t terminal root C sf d g
  refine ⟨min δB δP, lt_min hδB hδP, ?_⟩
  refine {
    number_selected := ⟨number_selected_positive T A hA Λ ℓ D t terminal root C g hℓ,
      number_selected_le_number_retained T A hA Λ ℓ D t terminal root C sf d⟩
    quasiErgodic := ?_
    support := ?_
    uniqueness := ?_
    distinct := ?_
    uniform_prefix := ?_
    all_stable := every_stable_start_literal_limit T A hA Λ ℓ D t terminal root C sf d g
    equilibrium_limit := liveLaw_tendsto_equilibrium T A hA Λ ℓ D t terminal root C sf d
    absorption := every_control_absorption T A hA Λ ℓ D t terminal root C g c hc hnoise }
  · intro ε hε hsmall s
    exact selected_literal_QEM T A hA Λ ℓ D t terminal root C sf d g s ε hε
      ((hsmall.trans_le (min_le_left _ _)).trans_le (hbase s))
  · intro ε hε hsmall s
    exact selected_core_support T A hA Λ ℓ D t terminal root C sf d s ε hε
      ((hsmall.trans_le (min_le_left _ _)).trans_le (hbase s))
  · intro ε hε hsmall s η hη hsupp
    exact selected_literal_QEM_unique_with_core_support T A hA Λ ℓ D t terminal root C sf d g
      s ε hε ((hsmall.trans_le (min_le_left _ _)).trans_le (hbase s)) η hη hsupp
  · intro ε hε hsmall s q he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hsq | hqs
    · exact liveLaw_pairwise_distinct T A hA Λ ℓ D t terminal root C sf d ε hε
        (fun s => (hsmall.trans_le (min_le_left _ _)).trans_le (hbase s)) hsq he
    · exact liveLaw_pairwise_distinct T A hA Λ ℓ D t terminal root C sf d ε hε
        (fun s => (hsmall.trans_le (min_le_left _ _)).trans_le (hbase s)) hqs he.symm
  · intro j
    obtain ⟨s, hs⟩ := hprefix j
    refine ⟨s, ?_⟩
    intro x hx happ
    obtain ⟨hxl, hlim⟩ := hs x hx happ
    exact ⟨hxl, fun ε hε hsmall => hlim ε hε (hsmall.trans_le (min_le_right _ _))⟩

end ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Conclusions
