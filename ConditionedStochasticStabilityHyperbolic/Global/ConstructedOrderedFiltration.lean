module

public import ConditionedStochasticStabilityHyperbolic.Global.FiniteBasicAdaptedFiltration
public import ConditionedStochasticStabilityHyperbolic.Global.PressurePrefixSelection
public import ConditionedStochasticStabilityHyperbolic.Global.AllShiftNullBoundaryFiltration
public import ConditionedStochasticStabilityHyperbolic.Global.PeriodicDenseBasicPartition
public import LeanShared.Dynamics.AbsorbingBaseReplacement
public import LeanShared.Dynamics.StrictTrappingBasicPartition

/-! Construct the actual fixed-absorber filtration in the prescribed reverse
graph order. The finite trapping levels are produced by the proved no-cycle
induction, starting at `closure A`; one-step absorption then replaces only
level zero by the original `A`. Strict trapping and the absorbed/retained
basic-set partition remain explicit geometric inputs. -/

public noncomputable section
open Set Function Bundle MeasureTheory
open scoped Topology Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Global.ConstructedOrderedFiltration
open LeanShared ShiftedFiltrationGeometry PressureFiltrationSource

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} (D : Paper.SpectralDecomposition (E := E) T)

theorem exists_ordered_source (A : Set M) (openA : IsOpen A)
    (strict : MapsTo T (closure A) A)
    (partition : ∀ j, D.core j ⊆ A ∨ D.core j ⊆ interior Aᶜ)
    (L : List (Fin D.count)) (positive : 0 < L.length) (nodup : L.Nodup)
    (cover : ∀ j, j ∈ L ↔ D.core j ⊆ Aᶜ)
    (ordered : ∀ i j : Fin L.length, D.edge (L.get i) (L.get j) → i < j) :
    ∃ S : AdaptedSource T A D.core L.length, S.index = reversedVertex L := by
  let J := {j | D.core j ⊆ A}
  let v := reversedVertex L
  have vertex_mem (k : Fin L.length) : v k ∈ L := List.get_mem _ _
  have retained (k : Fin L.length) : D.core (v k) ⊆ Aᶜ := (cover _).mp (vertex_mem k)
  have fresh (k : Fin L.length) : v k ∉ J := by
    intro absorbed
    obtain ⟨x, hx⟩ := (D.basic (v k)).nonempty
    exact retained k hx (absorbed hx)
  have onto (j : Fin D.count) (live : D.core j ⊆ Aᶜ) : ∃ k, v k = j := by
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp ((cover j).mpr live)
    refine ⟨⟨L.length - 1 - k.val, by omega⟩, ?_⟩
    change L.get ⟨L.length - 1 - (L.length - 1 - k.val), by omega⟩ = j
    have sameIndex : (⟨L.length - 1 - (L.length - 1 - k.val), by omega⟩ : Fin L.length) = k :=
      Fin.ext (by dsimp; omega)
    rw [sameIndex]
    exact hk
  have contains (j : Fin D.count) (hj : j ∈ J) : D.core j ⊆ interior (closure A) :=
    hj.trans (interior_maximal subset_closure openA)
  have excludes (j : Fin D.count) (hj : j ∉ J) : Disjoint (D.core j) (closure A) := by
    have live := (partition j).resolve_left hj
    apply Set.disjoint_left.mpr
    intro x hx member
    have separated := live hx
    rw [interior_compl] at separated
    exact separated member
  have covered (j : Fin D.count) : j ∈ J ∨ ∃ k, v k = j := by
    rcases partition j with absorbed | live
    · exact Or.inl absorbed
    · exact Or.inr (onto j (live.trans interior_subset))
  have compatible (k : Fin L.length) (j : Fin D.count) (edge : D.edge (v k) j) :
      j ∈ FiniteBasicAdaptedFiltration.corePrefix D J v k.val := by
    rcases covered j with absorbed | ⟨i, rfl⟩
    · exact Or.inl absorbed
    · have relation := ordered
        ⟨L.length - 1 - k.val, by omega⟩ ⟨L.length - 1 - i.val, by omega⟩ edge
      have numerical : L.length - 1 - k.val < L.length - 1 - i.val := relation
      exact Or.inr ⟨i, by omega, rfl⟩
  obtain ⟨S, index⟩ := FiniteBasicAdaptedFiltration.exists_source_from_trapping_base D
    isClosed_closure.isCompact (fun _ hx => (interior_maximal subset_closure openA) (strict hx))
    J contains excludes positive v (PressurePrefixSelection.reversedVertex_injective L nodup)
    fresh covered compatible
  let F (n : ℕ) := if n = 0 then A else S.levels n
  have positive_level (n : ℕ) (hn : 0 < n) : F n = S.levels n := ite_eq_right (by omega)
  have zero : F 0 = A := ite_eq_left rfl
  have monotone : Monotone F := by
    intro i j bound x hx
    by_cases first : i = 0
    · subst i
      rw [zero] at hx
      by_cases nextZero : j = 0
      · subst j
        exact zero.symm ▸ hx
      · rw [positive_level j (by omega)]
        exact S.monotone (Nat.zero_le j) (S.zero.symm ▸ subset_closure hx)
    · have positiveJ : 0 < j := by omega
      rw [positive_level i (by omega)] at hx
      rw [positive_level j positiveJ]
      exact S.monotone bound hx
  refine ⟨{
    levels := F
    index := v
    zero := zero
    monotone := monotone
    absorbing_forward := fun _ hx => strict (subset_closure hx)
    compact_positive := fun n hn bound => positive_level n hn ▸ S.compact_positive n hn bound
    adapted_positive := fun n hn bound => positive_level n hn ▸ S.adapted_positive n hn bound
    terminal := (positive_level L.length positive).trans S.terminal
    literal_core := ?_ }, rfl⟩
  intro i
  have original := S.literal_core i
  rw [index] at original
  change isolatedCore T (F (i.val+1) \ F i.val) = D.core (v i)
  rw [positive_level (i.val+1) (by omega)]
  by_cases first : i.val = 0
  · have core : isolatedCore T (S.levels 1 \ closure A) = D.core (v i) := by
      simpa only [filtrationLayer, first, zero_add, S.zero] using original
    rw [first, zero_add, zero]
    exact (isolatedCore_replace_absorbing_base T (S.levels 1) A (closure A)
      (fun x hx => ⟨1, by simpa only [iterate_one] using strict hx⟩) (by
        rw [core]
        exact Set.disjoint_left.mpr (fun x hx ha => retained i hx ha))).trans core
  · rw [positive_level i.val (by omega)]
    exact original

theorem exists_ordered_source_of_periodic_density
    (periodic_dense : closure (periodicPts (T : M → M)) = Paper.nonwanderingSet T)
    (A : Set M) (openA : IsOpen A) (strict : MapsTo T (closure A) A)
    (L : List (Fin D.count)) (positive : 0 < L.length) (nodup : L.Nodup)
    (cover : ∀ j, j ∈ L ↔ D.core j ⊆ Aᶜ)
    (ordered : ∀ i j : Fin L.length, D.edge (L.get i) (L.get j) → i < j) :
    ∃ S : AdaptedSource T A D.core L.length, S.index = reversedVertex L :=
  exists_ordered_source D A openA strict
    (PeriodicDenseBasicPartition.dichotomy D periodic_dense A openA strict)
    L positive nodup cover ordered

variable [MeasurableSpace M] [BorelSpace M]

theorem exists_ordered_null_source
    (periodic_dense : closure (periodicPts (T : M → M)) = Paper.nonwanderingSet T)
    (A : Set M) (openA : IsOpen A) (strict : MapsTo T (closure A) A)
    (L : List (Fin D.count)) (positive : 0 < L.length) (nodup : L.Nodup)
    (cover : ∀ j, j ∈ L ↔ D.core j ⊆ Aᶜ)
    (ordered : ∀ i j : Fin L.length, D.edge (L.get i) (L.get j) → i < j)
    (μ : Measure M) [IsFiniteMeasure μ] :
    ∃ S : AdaptedSource T A D.core L.length, S.index = reversedVertex L ∧
      (∀ N j, 0 < j → j ≤ L.length →
        μ (frontier (levels T A D.core L.length N S j)) = 0) ∧
      ∀ N (i : Fin L.length),
        μ (closure (filtrationLayer (levels T A D.core L.length N S) i.val) \
          filtrationLayer (levels T A D.core L.length N S) i.val) = 0 := by
  obtain ⟨original, index⟩ := exists_ordered_source_of_periodic_density D periodic_dense
    A openA strict L positive nodup cover ordered
  obtain ⟨S, sameIndex, boundary⟩ := AllShiftNullBoundaryFiltration.exists_replacement
    T A D.core L.length original μ
  exact ⟨S, sameIndex.trans index, boundary, fun N i =>
    AllShiftNullBoundaryFiltration.closed_layer_extra_zero T A openA D.core L.length N S μ
      (boundary N) i⟩

theorem exists_ordered_product_null_source {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace (M × Y)] [BorelSpace (M × Y)]
    (periodic_dense : closure (periodicPts (T : M → M)) = Paper.nonwanderingSet T)
    (A : Set M) (openA : IsOpen A) (strict : MapsTo T (closure A) A)
    (L : List (Fin D.count)) (positive : 0 < L.length) (nodup : L.Nodup)
    (cover : ∀ j, j ∈ L ↔ D.core j ⊆ Aᶜ)
    (ordered : ∀ i j : Fin L.length, D.edge (L.get i) (L.get j) → i < j)
    (μ : Measure (M × Y)) [IsFiniteMeasure μ] :
    ∃ S : AdaptedSource T A D.core L.length, S.index = reversedVertex L ∧
      (∀ N j, 0 < j → j ≤ L.length →
        μ (frontier (levels T A D.core L.length N S j ×ˢ (univ : Set Y))) = 0) ∧
      ∀ N (i : Fin L.length),
        μ ((closure (filtrationLayer (levels T A D.core L.length N S) i.val) \
          filtrationLayer (levels T A D.core L.length N S) i.val) ×ˢ (univ : Set Y)) = 0 := by
  obtain ⟨S, index, boundary, extra⟩ := exists_ordered_null_source D periodic_dense
    A openA strict L positive nodup cover ordered (μ.map Prod.fst)
  refine ⟨S, index, ?_, ?_⟩
  · intro N j hj bound
    have null := boundary N j hj bound
    rw [Measure.map_apply continuous_fst.measurable isClosed_frontier.measurableSet] at null
    rw [frontier_prod_univ_eq]
    simpa only [prod_univ] using null
  · intro N i
    have lower : MeasurableSet (levels T A D.core L.length N S i.val) := by
      by_cases first : i.val = 0
      · rw [first, levels_zero]
        exact openA.measurableSet
      · exact (levels_positive_compact T A D.core L.length N S i.val
          (Nat.pos_of_ne_zero first) (by omega)).measurableSet
    have stratum : MeasurableSet (filtrationLayer (levels T A D.core L.length N S) i.val) :=
      (levels_positive_compact T A D.core L.length N S (i.val+1)
        (by omega) (by omega)).measurableSet.diff lower
    have null := extra N i
    rw [Measure.map_apply continuous_fst.measurable
      (isClosed_closure.measurableSet.diff stratum)] at null
    simpa only [prod_univ] using null

end ConditionedStochasticStabilityHyperbolic.Global.ConstructedOrderedFiltration
