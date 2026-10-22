module

public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Application
public import ConditionedStochasticStabilityHyperbolic.Global.ActualStablePrefixEntry

/-! # All stable basins for the derived selected HG2 family

The additional data are ordinary deterministic basin connections, the actual
noise model and the already proved finite graph assignment. No initial
positivity, live-orbit assertion, QEM or conditioned limit is supplied.
-/
@[expose] public noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Basins
open AbsorbingMarkovChains LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry
open ActualFiltrationGrowth ActualPrefixBasicGeometry DerivedHG2Application
open ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic LeanShared.ControlledPlaqueClosure
variable {X I Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]

abbrev originalIndex {ℓ : ℕ} {k : Fin ℓ} (i : Fin (k.val + 1)) : Fin ℓ :=
  ⟨i.val, by have h := i.isLt; have hh := k.isLt; omega⟩

structure GeometricSources
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
    (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
    (root : ∀ s, Fin ((terminal s).val + 1)) (C : NNReal → CanonicalChain X) where
  strict_trapping : MapsTo T (closure A) A
  separation : ∀ i, Λ i ⊆ interior Aᶜ
  transitive : ∀ i : Fin ℓ, forwardTransitiveOn T (Λ (D.index i))
  noise : NNReal → Measure Ω
  probability : ∀ ε, IsProbabilityMeasure (noise ε)
  open_positive : ∀ ε, 0 < ε → (noise ε).IsOpenPosMeasure
  maps : NNReal → X × Ω → X
  measurable : ∀ ε, Measurable (maps ε)
  continuous : ∀ ε, 0 < ε → Continuous (maps ε)
  potential : X → ℝ
  potential_measurable : Measurable potential
  R : ℝ
  R_positive : 0 < R
  weight_bound : ∀ x, Real.exp (potential x) ≤ R
  actual_model : ∀ ε, (C ε).killedTransition =
    (NoiseKernel.chain (noise ε) (maps ε) (measurable ε) Aᶜ hA.measurableSet.compl
      (fun x => Real.exp (potential x)) (Real.measurable_exp.comp potential_measurable)
      R R_positive weight_bound).killedTransition
  zero_control : Ω
  zero_map : ∀ ε, 0 < ε → ∀ x, maps ε (x, zero_control) = T x
  radius : NNReal → ℝ
  radius_positive : ∀ ε, 0 < ε → 0 < radius ε
  image_ball : ∀ ε, 0 < ε → ∀ z ∈ interior Aᶜ, ∀ y ∈ interior Aᶜ,
    dist (T z) y < radius ε → ∃ ω, maps ε (z, ω) = y
  edge : Fin ℓ → Fin ℓ → Prop
  connections : ∀ i j, edge i j → ∃ z : X,
    (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index j), dist ((T : X → X)^[n + 1] z) y < r) ∧
    (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index i), dist ((T.symm : X → X)^[n] z) y < r)
  assignment : ∀ j : Fin ℓ, ∃ s : Fin t, ∃ i : Fin ((terminal s).val + 1),
    Λ (D.index j) = Λ (D.index (originalIndex i)) ∧
      Relation.ReflTransGen (fun a b => edge (originalIndex a) (originalIndex b)) i (root s)

variable (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → CanonicalChain X) (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))
  (d : Families T A hA Λ ℓ D t terminal root C sf)
  (g : GeometricSources (Ω := Ω) T A hA Λ ℓ D t terminal root C)

local instance prefixCompact (s : Fin t) (N : ℕ) : CompactSpace (actualPrefix T A Λ ℓ D (terminal s) N) :=
  isCompact_iff_compactSpace.mp (levels_positive_compact T A Λ ℓ N D ((terminal s).val + 1) (by omega) (by have h := (terminal s).isLt; omega))

def fullMeasure (s : Fin t) (N : ℕ) (ε : NNReal) (hε : 0 < ε) (hs : ε < d.window s N) : Measure X :=
  (productMeasure
    (chain (C ε) (actualPrefix T A Λ ℓ D (terminal s) N)
      (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1)))
    (strongFeller (C ε) (sf ε hε) (actualPrefix T A Λ ℓ D (terminal s) N)
      (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1)))
    (d.data s N ε hε hs)).map Subtype.val

omit [CompactSpace X] in
/-- All actual prefix starts in an assigned stable basin converge without
any supplied positivity or live-orbit premise. -/
theorem stable_limit_on_shifted_prefix
    (s : Fin t) (N : ℕ) (ε : NNReal) (hε : 0 < ε) (hs : ε < d.window s N)
    (i : Fin ((terminal s).val + 1))
    (hreach : Relation.ReflTransGen (fun a b => g.edge (originalIndex a) (originalIndex b)) i (root s))
    (x : actualPrefix T A Λ ℓ D (terminal s) N)
    (happroach : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index (originalIndex i)),
      dist ((T : X → X)^[n + 1] x.val) y < r)
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) :
    Tendsto (MeasurableCanonical.pathAverage (C ε) f x.val) atTop
      (𝓝 (∫ y, f y ∂fullMeasure T A hA Λ ℓ D t terminal root C sf d s N ε hε hs)) := by
  let : IsProbabilityMeasure (g.noise ε) := g.probability ε
  let : (g.noise ε).IsOpenPosMeasure := g.open_positive ε hε
  let selected : Set (actualPrefix T A Λ ℓ D (terminal s) N) :=
    {y | y.val ∈ Λ (D.index (originalIndex (root s)))}
  have hcoreImage : Λ (D.index (originalIndex (root s))) = Subtype.val '' selected := by
    ext y
    constructor
    · intro hy
      have hp := (actual_prefix_basic_properties T A hA Λ ℓ N D g.separation
        ((terminal s).val + 1) (by have h := (terminal s).isLt; omega) (root s)).2.2.2 hy
      exact ⟨⟨y, interior_subset hp.1⟩, hy, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp
  exact FiltrationSelectedStableBasin.full_conditioned_limit_from_literal_prefix_geometry
    T A hA Λ ℓ N D g.separation ((terminal s).val + 1) (by omega) (by have h := (terminal s).isLt; omega)
    (C ε) (sf ε hε) (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1))
    (d.invariant s N ε hε hs) (d.data s N ε hε hs) selected
    (fun y hy => d.core_positive s N ε hε hs y hy)
    (g.noise ε) (g.maps ε) (g.measurable ε) (g.continuous ε hε)
    Aᶜ hA.measurableSet.compl (interior Aᶜ) isOpen_interior interior_subset
    g.potential g.potential_measurable g.R g.R_positive g.weight_bound
    (g.actual_model ε) g.strict_trapping rfl g.zero_control (g.zero_map ε hε)
    (fun i => g.transitive (originalIndex i)) (g.radius_positive ε hε)
    (fun z hz y hy hd => g.image_ball ε hε z hz.2 y hy.2 hd)
    (fun a b => g.edge (originalIndex a) (originalIndex b))
    (fun a b hab => g.connections (originalIndex a) (originalIndex b) hab)
    hreach hcoreImage x happroach f hf hb

include g in
omit [CompactSpace X] in
theorem shifted_products_eq_base (s : Fin t) (N : ℕ) (ε : NNReal) (hε : 0 < ε)
    (hbase : ε < d.window s 0) (hs : ε < d.window s N) :
    fullMeasure T A hA Λ ℓ D t terminal root C sf d s N ε hε hs =
      fullMeasure T A hA Λ ℓ D t terminal root C sf d s 0 ε hε hbase := by
  obtain ⟨p, hp⟩ := d.core_nonempty s
  have hpi := (actual_prefix_basic_properties T A hA Λ ℓ 0 D g.separation
    ((terminal s).val + 1) (by have h := (terminal s).isLt; omega) (root s)).2.2.2 hp
  let p₀ : actualPrefix T A Λ ℓ D (terminal s) 0 := ⟨p, interior_subset hpi.1⟩
  exact ShiftedPrefixIdentification.actual_prefix_products_eq (C ε) (sf ε hε)
    (actualPrefix T A Λ ℓ D (terminal s) 0) (actualPrefix T A Λ ℓ D (terminal s) N)
    (ambient_levels_measurable T A hA Λ ℓ 0 D ((terminal s).val + 1))
    (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1))
    (d.invariant s 0 ε hε hbase) (d.invariant s N ε hε hs)
    (d.data s 0 ε hε hbase) (d.data s N ε hε hs) p₀ hpi.1
    (d.core_positive s 0 ε hε hbase p₀ hp) (d.core_support s N ε hε hs hp)

omit [CompactSpace X] in
theorem stable_limit_to_original_live_probability
    (s : Fin t) (N : ℕ) (ε : NNReal) (hε : 0 < ε)
    (hbase : ε < d.window s 0) (hs : ε < d.window s N)
    (i : Fin ((terminal s).val + 1))
    (hreach : Relation.ReflTransGen (fun a b => g.edge (originalIndex a) (originalIndex b)) i (root s))
    (x : actualPrefix T A Λ ℓ D (terminal s) N)
    (happroach : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index (originalIndex i)),
      dist ((T : X → X)^[n + 1] x.val) y < r)
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) :
    Tendsto (MeasurableCanonical.pathAverage (C ε) f x.val) atTop
      (𝓝 (∫ y, f y.val ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)))) := by
  have hlim := stable_limit_on_shifted_prefix T A hA Λ ℓ D t terminal root C sf d g
    s N ε hε hs i hreach x happroach f hf hb
  rw [shifted_products_eq_base T A hA Λ ℓ D t terminal root C sf d g s N ε hε hbase hs] at hlim
  have hm : fullMeasure T A hA Λ ℓ D t terminal root C sf d s 0 ε hε hbase =
      (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)).map Subtype.val := by
    rw [fullMeasure, d.base_product_identity s ε hε hbase]
    exact (congrArg (fun ν : ProbabilityMeasure X => (ν : Measure X))
      (liveLaw_map T A hA Λ ℓ D t terminal root C sf d s ε)).symm
  rw [hm, (MeasurableEmbedding.subtype_coe hA.measurableSet.compl).integral_map f] at hlim
  exact hlim

include g in
omit [CompactSpace X] in
/-- Every retained basic set is assigned one selected probability. For every
stable starting state the noise window is chosen before the observable. -/
theorem every_retained_stable_start_has_selected_limit :
    ∀ j : Fin ℓ, ∃ s : Fin t, ∀ x : X,
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index j),
        dist ((T : X → X)^[n + 1] x) y < r) →
      ∃ δ : NNReal, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ →
        ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
          Tendsto (MeasurableCanonical.pathAverage (C ε) f x) atTop
            (𝓝 (∫ y, f y.val ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)))) := by
  intro j
  obtain ⟨s, i, hsets, hreach⟩ := g.assignment j
  refine ⟨s, ?_⟩
  intro x happroach
  have happ : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index (originalIndex i)),
      dist ((T : X → X)^[n + 1] x) y < r := by
    simpa only [hsets] using happroach
  have hinv := (actual_prefix_basic_properties T A hA Λ ℓ 0 D g.separation
    ((terminal s).val + 1) (by have h := (terminal s).isLt; omega) i).2.1
  obtain ⟨N, _hN, hx, _⟩ := ActualStablePrefixEntry.exists_actual_shifted_prefix_for_stable_start
    T A hA g.strict_trapping Λ ℓ D g.separation (originalIndex i)
    ((terminal s).val + 1) i.isLt (by have h := (terminal s).isLt; omega) hinv x happ
  refine ⟨min (d.window s 0) (d.window s N), lt_min (d.window_positive s 0) (d.window_positive s N), ?_⟩
  intro ε hε hsmall f hf hb
  exact stable_limit_to_original_live_probability T A hA Λ ℓ D t terminal root C sf d g
    s N ε hε (hsmall.trans_le (min_le_left _ _)) (hsmall.trans_le (min_le_right _ _))
    i hreach ⟨x, interior_subset hx⟩ happ f hf hb

include g in
omit [CompactSpace X] in
/-- One original-prefix window works before all basic-set basins, starting
states, and bounded measurable observables, as in global-global(i). -/
theorem exists_uniform_original_prefix_basin_window :
    ∃ δ : NNReal, 0 < δ ∧ ∀ j : Fin ℓ, ∃ s : Fin t,
      ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) 0,
        (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index j),
          dist ((T : X → X)^[n + 1] x) y < r) →
        ∀ ε, 0 < ε → ε < δ → ∀ f : X → ℝ, Measurable f →
          (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
            Tendsto (MeasurableCanonical.pathAverage (C ε) f x) atTop
              (𝓝 (∫ y, f y.val ∂(liveLaw T A hA Λ ℓ D t terminal root C sf d s ε : Measure ↥(Aᶜ)))) := by
  obtain ⟨δ, hδ, hwindow⟩ := exists_common_base_window T A hA Λ ℓ D t terminal root C sf d
  refine ⟨δ, hδ, ?_⟩
  intro j
  obtain ⟨s, i, hsets, hreach⟩ := g.assignment j
  refine ⟨s, ?_⟩
  intro x hx happroach ε hε hsmall f hf hb
  exact stable_limit_to_original_live_probability T A hA Λ ℓ D t terminal root C sf d g
    s 0 ε hε (hsmall.trans_le (hwindow s)) (hsmall.trans_le (hwindow s))
    i hreach ⟨x, hx⟩ (by simpa only [hsets] using happroach) f hf hb

end ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Basins
