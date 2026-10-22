module

public import ConditionedStochasticStabilityHyperbolic.Global.LivePrefixQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.LivePrefixPathAverage
public import ConditionedStochasticStabilityHyperbolic.Global.SelectedPrefixDistinctness
public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationStableLimit
public import ConditionedStochasticStabilityHyperbolic.Global.GlobalAbsorptionEveryControl
public import LeanShared.Probability.ClosedLiveWeakConvergence

/-! # Applying the derived HG2 finite-actualPrefix construction

This interface records intermediate OUTPUTS of the checked analytic, graph,
filtration and collar producers. It is not a classical theorem assumption or
an encoding of HG2. No full-process QEM, stable-start limit, global weak limit
or absorption conclusion is a field. The final physical-model constructor
must construct this derived interface from the precise cited local sources.
-/
@[expose] public noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Application
open AbsorbingMarkovChains LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry
open ActualFiltrationGrowth FiltrationPressureConfinement ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic
variable {X I : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

abbrev actualPrefix (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : Fin ℓ) (N : ℕ) := levels T A Λ ℓ N D (k.val + 1)

local instance prefixCompact (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : Fin ℓ) (N : ℕ) : CompactSpace (actualPrefix T A Λ ℓ D k N) :=
  isCompact_iff_compactSpace.mp (levels_positive_compact T A Λ ℓ N D (k.val + 1) (by omega) (by omega))

structure Families
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
    (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
    (root : ∀ s, Fin ((terminal s).val + 1))
    (C : NNReal → CanonicalChain X) (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε)) where
  window : Fin t → ℕ → NNReal
  window_positive : ∀ s N, 0 < window s N
  data : ∀ s N ε (hε : 0 < ε), ε < window s N →
    RankOneSpectralData (transferOperator (𝕜 := ℝ)
      (chain (C ε) (actualPrefix T A Λ ℓ D (terminal s) N)
        (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1)))
      (strongFeller (C ε) (sf ε hε) (actualPrefix T A Λ ℓ D (terminal s) N)
        (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1))))
      (1 : actualPrefix T A Λ ℓ D (terminal s) N →ᵇ ℝ)
  invariant : ∀ s N ε (_hε : 0 < ε), ε < window s N →
    ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) N,
      (C ε).killedTransition x (actualPrefix T A Λ ℓ D (terminal s) N)ᶜ = 0
  zero_absorbing : ∀ ε, 0 < ε → ∀ x, (C ε).killedTransition x A = 0
  core_nonempty : ∀ s, (Λ (D.index ⟨(root s).val, by have h := (root s).isLt; have _hh := (terminal s).isLt; omega⟩)).Nonempty
  core_positive : ∀ s N ε hε hs (x : actualPrefix T A Λ ℓ D (terminal s) N),
    x.val ∈ Λ (D.index ⟨(root s).val, by have h := (root s).isLt; have _hh := (terminal s).isLt; omega⟩) →
      0 < (data s N ε hε hs).eigenvector x
  core_support : ∀ s N ε hε hs,
    Λ (D.index ⟨(root s).val, by have h := (root s).isLt; have _hh := (terminal s).isLt; omega⟩) ⊆
      ((productMeasure
        (chain (C ε) (actualPrefix T A Λ ℓ D (terminal s) N)
          (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1)))
        (strongFeller (C ε) (sf ε hε) (actualPrefix T A Λ ℓ D (terminal s) N)
          (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1)))
        (data s N ε hε hs)).map Subtype.val).support
  closedProduct : ∀ s, NNReal → Measure (closedLayer T A Λ ℓ 0 D
    ⟨(root s).val, by have h := (root s).isLt; have _hh := (terminal s).isLt; omega⟩)
  base_product_identity : ∀ s ε hε hs,
    (productMeasure
      (chain (C ε) (actualPrefix T A Λ ℓ D (terminal s) 0)
        (ambient_levels_measurable T A hA Λ ℓ 0 D ((terminal s).val + 1)))
      (strongFeller (C ε) (sf ε hε) (actualPrefix T A Λ ℓ D (terminal s) 0)
        (ambient_levels_measurable T A hA Λ ℓ 0 D ((terminal s).val + 1)))
      (data s 0 ε hε hs)).map Subtype.val = (closedProduct s ε).map Subtype.val
  root_above_later : ∀ s q : Fin t, s < q → (terminal q).val + 1 ≤ (root s).val
  closedProduct_probability : ∀ s ε, IsProbabilityMeasure (closedProduct s ε)
  equilibrium : Fin t → ProbabilityMeasure ↥(Aᶜ)
  localWeak : ∀ s, Tendsto
    (fun ε => ProbabilityMeasure.map (⟨closedProduct s ε, closedProduct_probability s ε⟩ : ProbabilityMeasure
      (closedLayer T A Λ ℓ 0 D
        ⟨(root s).val, by have h := (root s).isLt; have _hh := (terminal s).isLt; omega⟩)) Subtype.val)
    (𝓝[>] 0) (𝓝 (ProbabilityMeasure.map (equilibrium s) (Subtype.val : ↥(Aᶜ) → X)))

variable (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → CanonicalChain X) (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))
  (d : Families T A hA Λ ℓ D t terminal root C sf)

include hA in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Literal closed analytic layers never contain the fixed open absorbing
region; no nullity or regularity of its boundary is used. -/
theorem closedLayer_subset_live (j : Fin ℓ) : closedLayer T A Λ ℓ 0 D j ⊆ Aᶜ := by
  apply closure_minimal _ hA.isClosed_compl
  intro x hx hxA
  exact hx.2 (levels_monotone T A Λ ℓ 0 D (Nat.zero_le j.val)
    ((levels_zero T A Λ ℓ 0 D).symm ▸ hxA))

/-- The selected probabilities on the exact closed live state space. -/
def liveProbability (s : Fin t) (ε : NNReal) : Measure ↥(Aᶜ) :=
  (d.closedProduct s ε).map (fun x =>
    (⟨x.val, closedLayer_subset_live T A hA Λ ℓ D _ x.property⟩ : ↥(Aᶜ)))

omit [CompactSpace X] in
/-- Every derived selected-actualPrefix product is an actual live-process QEM,
including selected roots which are not globally dominant. -/
theorem liveProbability_isQuasiErgodic (s : Fin t) (ε : NNReal) (hε : 0 < ε)
    (hs : ε < d.window s 0) :
    (chain (C ε) Aᶜ hA.measurableSet.compl).IsQuasiErgodic
      (liveProbability T A hA Λ ℓ D t terminal root C sf d s ε) := by
  have hq := PrefixQuasiErgodic.full_process_isQuasiErgodic_of_prefix (C ε)
    (actualPrefix T A Λ ℓ D (terminal s) 0)
    (ambient_levels_measurable T A hA Λ ℓ 0 D ((terminal s).val + 1))
    (d.invariant s 0 ε hε hs) _
    (productMeasure_isQuasiErgodic _ _ (d.data s 0 ε hε hs))
  rw [d.base_product_identity s ε hε hs] at hq
  exact LivePrefixQuasiErgodic.live_QEM_of_produced_closed_product (C ε) Aᶜ _
    hA.measurableSet.compl (closedLayer_subset_live T A hA Λ ℓ D _)
    (by intro x hx; simpa only [compl_compl] using d.zero_absorbing ε hε x)
    (d.closedProduct s ε) hq

/-- An actual probability family on the literal live space, including a
harmless local-family continuation outside the proof window. -/
def liveLaw (s : Fin t) (ε : NNReal) : ProbabilityMeasure ↥(Aᶜ) := by
  let : IsProbabilityMeasure (d.closedProduct s ε) := d.closedProduct_probability s ε
  exact ⟨liveProbability T A hA Λ ℓ D t terminal root C sf d s ε,
    (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.subtype_mk.aemeasurable).mpr inferInstance⟩

omit [CompactSpace X] in
theorem liveLaw_map (s : Fin t) (ε : NNReal) :
    (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε).map
      (Subtype.val : ↥(Aᶜ) → X) =
      ProbabilityMeasure.map (⟨d.closedProduct s ε, d.closedProduct_probability s ε⟩ : ProbabilityMeasure _) Subtype.val := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map Subtype.val (Measure.map _ _) = _
  rw [Measure.map_map measurable_subtype_coe measurable_subtype_coe.subtype_mk]
  rfl

omit [CompactSpace X] in
/-- Local physical weak convergence gives weak convergence of the actual
selected global live probabilities by their exact state inclusions. -/
theorem liveLaw_tendsto_equilibrium (s : Fin t) :
    Tendsto (liveLaw T A hA Λ ℓ D t terminal root C sf d s) (𝓝[>] 0) (𝓝 (d.equilibrium s)) := by
  apply LeanShared.ClosedLiveWeakConvergence.tendsto_of_map_subtype hA.isClosed_compl
  have he : ∀ ε, (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε).map
      (Subtype.val : ↥(Aᶜ) → X) =
      ProbabilityMeasure.map (⟨d.closedProduct s ε, d.closedProduct_probability s ε⟩ : ProbabilityMeasure _) Subtype.val := by
    intro ε
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map Subtype.val (Measure.map _ _) = _
    rw [Measure.map_map measurable_subtype_coe measurable_subtype_coe.subtype_mk]
    rfl
  simpa only [he] using d.localWeak s

omit [CompactSpace X] in
theorem exists_common_base_window :
    ∃ δ : NNReal, 0 < δ ∧ ∀ s : Fin t, δ ≤ d.window s 0 := by
  classical
  by_cases ht : Nonempty (Fin t)
  · have hU : (Finset.univ : Finset (Fin t)).Nonempty := by
      obtain ⟨s⟩ := ht
      exact ⟨s, Finset.mem_univ s⟩
    exact ⟨Finset.univ.inf' hU (fun s => d.window s 0),
      (Finset.lt_inf'_iff hU).mpr (fun s _ => d.window_positive s 0),
      fun s => Finset.inf'_le _ (Finset.mem_univ s)⟩
  · exact ⟨1, zero_lt_one, fun s => False.elim (ht ⟨s⟩)⟩

omit [CompactSpace X] in
/-- The finite selected-family existence and stochastic-stability conclusions
hold on one window chosen before all selected blocks. -/
theorem exists_common_window_live_QEM_and_weak_limit :
    ∃ δ : NNReal, 0 < δ ∧
      (∀ ε, 0 < ε → ε < δ → ∀ s : Fin t,
        (chain (C ε) Aᶜ hA.measurableSet.compl).IsQuasiErgodic
          (liveLaw T A hA Λ ℓ D t terminal root C sf d s ε)) ∧
      ∀ s : Fin t, Tendsto (liveLaw T A hA Λ ℓ D t terminal root C sf d s)
        (𝓝[>] 0) (𝓝 (d.equilibrium s)) := by
  obtain ⟨δ, hδ, hs⟩ := exists_common_base_window T A hA Λ ℓ D t terminal root C sf d
  refine ⟨δ, hδ, ?_, liveLaw_tendsto_equilibrium T A hA Λ ℓ D t terminal root C sf d⟩
  intro ε hε hεδ s
  exact liveProbability_isQuasiErgodic T A hA Λ ℓ D t terminal root C sf d s ε hε
    (hεδ.trans_le (hs s))

omit [CompactSpace X] in
/-- Different selected blocks give different actual live probabilities. -/
theorem liveLaw_pairwise_distinct (ε : NNReal) (hε : 0 < ε)
    (hsmall : ∀ s, ε < d.window s 0) {s q : Fin t} (hsq : s < q) :
    liveLaw T A hA Λ ℓ D t terminal root C sf d s ε ≠
      liveLaw T A hA Λ ℓ D t terminal root C sf d q ε := by
  let j : Fin ℓ := ⟨(root s).val, by have h := (root s).isLt; have hh := (terminal s).isLt; omega⟩
  have hsupport : Λ (D.index j) ⊆ ((d.closedProduct s ε).map Subtype.val).support := by
    have h := d.core_support s 0 ε hε (hsmall s)
    rw [d.base_product_identity s ε hε (hsmall s)] at h
    exact h
  have hne := SelectedPrefixDistinctness.actual_selected_products_ne T A Λ ℓ 0 D
    ((terminal q).val + 1) (by omega) (by have h := (terminal q).isLt; omega)
    j (d.root_above_later s q hsq) (d.core_nonempty s)
    (productMeasure
      (chain (C ε) (actualPrefix T A Λ ℓ D (terminal q) 0)
        (ambient_levels_measurable T A hA Λ ℓ 0 D ((terminal q).val + 1)))
      (strongFeller (C ε) (sf ε hε) (actualPrefix T A Λ ℓ D (terminal q) 0)
        (ambient_levels_measurable T A hA Λ ℓ 0 D ((terminal q).val + 1)))
      (d.data q 0 ε hε (hsmall q)))
    ((d.closedProduct s ε).map Subtype.val) hsupport
  intro he
  apply hne
  rw [d.base_product_identity q ε hε (hsmall q)]
  have hm := congrArg (fun ν : ProbabilityMeasure ↥(Aᶜ) =>
    (ν.map (Subtype.val : ↥(Aᶜ) → X) : Measure X)) he
  rw [liveLaw_map T A hA Λ ℓ D t terminal root C sf d s ε,
    liveLaw_map T A hA Λ ℓ D t terminal root C sf d q ε] at hm
  exact hm.symm

end ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Application
