module

public import ConditionedStochasticStabilityHyperbolic.Global.BasicSetFiltrationStep
public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry
public import LeanShared.Dynamics.PressureTopologicalOrder

/-! A finite compatible enumeration is turned into an actual adapted
filtration by the proved compact trapping extension. No adapted-filtration
existence statement is an input. -/

public noncomputable section
open Set Function Bundle
open scoped Topology Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Global.FiniteBasicAdaptedFiltration
open BasicSetFiltrationStep LeanShared ShiftedFiltrationGeometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} (D : Paper.SpectralDecomposition (E := E) T)

theorem terminal_layer_core {C : Set M} (J : Set (Fin D.count))
    (contains : ∀ j ∈ J, D.core j ⊆ interior C)
    (excludes : ∀ j ∉ J, Disjoint (D.core j) C)
    {i : Fin D.count} (fresh : i ∉ J)
    (last : ∀ j, j ∈ J ∨ j = i) (targets : ∀ j, D.edge i j → j ∈ J) :
    isolatedCore T (univ \ C) = D.core i := by
  apply Subset.antisymm
  · intro x hx
    have classify (R : M ≃ₜ M) (j : Fin D.count)
        (trapped : x ∈ forwardTrapped R (univ \ C))
        (basin : x ∈ PaperStableBasin.stableBasin R (D.core j)) : j = i := by
      rcases last j with old | same
      · obtain ⟨n, hit⟩ := stableBasin_enters_open R (D.basic j).hyperbolic.compact
          isOpen_interior (contains j old) basin
        exact False.elim ((trapped n).2 (interior_subset hit))
      · exact same
    obtain ⟨j, past⟩ := BasicSetBasinDecomposition.backward D x
    obtain ⟨k, future⟩ := BasicSetBasinDecomposition.forward D x
    have pastSame := classify T.symm j hx.2 past
    have futureSame := classify T k hx.1 future
    subst j
    subst k
    by_contra outside
    exact fresh (targets i ⟨x, ⟨past, outside⟩, ⟨future, outside⟩⟩)
  · intro x hx
    have member (y : M) (hy : y ∈ D.core i) : y ∈ univ \ C :=
      ⟨mem_univ _, fun hc => Set.disjoint_left.mp (excludes i fresh) hy hc⟩
    have original := (D.basic i).isolated ▸ hx
    refine ⟨fun n => member _ ?_, fun n => member _ ?_⟩
    · simpa only [← (D.basic i).isolated] using iterate_mem_isolatedCore T _ original n
    · simpa only [← (D.basic i).isolated] using iterate_symm_mem_isolatedCore T _ original n

@[expose] def corePrefix {ℓ : ℕ} (J : Set (Fin D.count)) (v : Fin ℓ → Fin D.count) (n : ℕ) :
    Set (Fin D.count) := J ∪ {j | ∃ k : Fin ℓ, k.val < n ∧ v k = j}

structure PrefixLevel {ℓ : ℕ} (J : Set (Fin D.count)) (v : Fin ℓ → Fin D.count)
    (n : ℕ) where
  level : Set M
  compact : IsCompact level
  trapping : MapsTo T level (interior level)
  contains : ∀ j ∈ corePrefix D J v n, D.core j ⊆ interior level
  excludes : ∀ j ∉ corePrefix D J v n, Disjoint (D.core j) level

omit [CompactSpace M] in
theorem prefix_zero {ℓ : ℕ} (J : Set (Fin D.count)) (v : Fin ℓ → Fin D.count) :
    corePrefix D J v 0 = J := by
  ext j
  simp only [corePrefix, mem_union, mem_ofPred_eq, Nat.not_lt_zero, false_and, exists_false, or_false]

omit [CompactSpace M] in
theorem prefix_succ {ℓ : ℕ} (J : Set (Fin D.count)) (v : Fin ℓ → Fin D.count)
    (n : Fin ℓ) : corePrefix D J v (n.val+1) = insert (v n) (corePrefix D J v n.val) := by
  ext j
  simp only [corePrefix, mem_union, mem_ofPred_eq, mem_insert_iff]
  constructor
  · rintro (old | ⟨k, hk, same⟩)
    · exact Or.inr (Or.inl old)
    · by_cases before : k.val < n.val
      · exact Or.inr (Or.inr ⟨k, before, same⟩)
      · have equal : k = n := Fin.ext (by omega)
        subst k
        exact Or.inl same.symm
  · rintro (rfl | old | ⟨k, hk, same⟩)
    · exact Or.inr ⟨n, by omega, rfl⟩
    · exact Or.inl old
    · exact Or.inr ⟨k, by omega, same⟩

theorem exists_successor {ℓ : ℕ} (J : Set (Fin D.count)) (v : Fin ℓ → Fin D.count)
    (injective : Injective v) (fresh : ∀ k, v k ∉ J)
    (ordered : ∀ k j, D.edge (v k) j → j ∈ corePrefix D J v k.val)
    (n : Fin ℓ) (C : PrefixLevel D J v n.val) :
    ∃ C' : PrefixLevel D J v (n.val+1), C.level ⊆ C'.level ∧
      isolatedCore T (C'.level \ C.level) = D.core (v n) := by
  have new : v n ∉ corePrefix D J v n.val := by
    rintro (old | ⟨k, before, same⟩)
    · exact fresh n old
    · have equal := injective same
      subst k
      exact (lt_irrefl n.val) before
  obtain ⟨next, compact, contains, trapping, cores, excludes, layer⟩ :=
    exists_next_level D C.compact C.trapping (corePrefix D J v n.val)
      C.contains C.excludes new (ordered n)
  exact ⟨⟨next, compact, trapping,
    by simpa only [prefix_succ] using cores,
    by simpa only [prefix_succ] using excludes⟩, contains, layer⟩

theorem exists_source_from_trapping_base {C : Set M} (compactC : IsCompact C)
    (trapping : MapsTo T C (interior C)) (J : Set (Fin D.count))
    (contains : ∀ j ∈ J, D.core j ⊆ interior C)
    (excludes : ∀ j ∉ J, Disjoint (D.core j) C)
    {ℓ : ℕ} (positive : 0 < ℓ) (v : Fin ℓ → Fin D.count)
    (injective : Injective v) (fresh : ∀ k, v k ∉ J)
    (cover : ∀ j, j ∈ J ∨ ∃ k, v k = j)
    (ordered : ∀ k j, D.edge (v k) j → j ∈ corePrefix D J v k.val) :
    ∃ S : AdaptedSource T C D.core ℓ, S.index = v := by
  let initial : PrefixLevel D J v 0 := ⟨C, compactC, trapping,
    by simpa only [prefix_zero] using contains,
    by simpa only [prefix_zero] using excludes⟩
  let next (n : Fin ℓ) (S : PrefixLevel D J v n.val) : PrefixLevel D J v (n.val+1) :=
    Classical.choose (exists_successor D J v injective fresh ordered n S)
  have next_spec (n : Fin ℓ) (S : PrefixLevel D J v n.val) :
      S.level ⊆ (next n S).level ∧
        isolatedCore T ((next n S).level \ S.level) = D.core (v n) :=
    Classical.choose_spec (exists_successor D J v injective fresh ordered n S)
  let chain : (n : Fin (ℓ+1)) → PrefixLevel D J v n.val :=
    Fin.induction initial (fun n previous => next n previous)
  have chain_step (n : Fin ℓ) :
      (chain n.castSucc).level ⊆ (chain n.succ).level ∧
        isolatedCore T ((chain n.succ).level \ (chain n.castSucc).level) = D.core (v n) := by
    exact next_spec n (chain n.castSucc)
  let levels (n : ℕ) : Set M := if h : n < ℓ then (chain ⟨n, by omega⟩).level else univ
  have level_before (n : ℕ) (h : n < ℓ) : levels n = (chain ⟨n, by omega⟩).level := dite_eq_left h
  have terminal (n : ℕ) (h : ℓ ≤ n) : levels n = univ := dite_eq_right (by omega)
  have zero : levels 0 = C := by
    rw [level_before 0 positive]
    rfl
  have monotone : Monotone levels := by
    apply monotone_nat_of_le_succ
    intro n
    by_cases before : n+1 < ℓ
    · rw [level_before n (by omega), level_before (n+1) before]
      exact (chain_step ⟨n, by omega⟩).1
    · rw [terminal (n+1) (by omega)]
      exact subset_univ _
  refine ⟨{
    levels := levels
    index := v
    zero := zero
    monotone := monotone
    absorbing_forward := fun _ hx => interior_subset (trapping hx)
    compact_positive := ?_
    adapted_positive := ?_
    terminal := terminal ℓ le_rfl
    literal_core := ?_ }, rfl⟩
  · intro n _positive _bound
    by_cases before : n < ℓ
    · rw [level_before n before]
      exact (chain ⟨n, by omega⟩).compact
    · rw [terminal n (by omega)]
      exact isCompact_univ
  · intro n _positive _bound
    by_cases before : n < ℓ
    · rw [level_before n before]
      exact (chain ⟨n, by omega⟩).trapping
    · rw [terminal n (by omega), interior_univ]
      exact mapsTo_univ _ _
  · intro n
    change isolatedCore T (levels (n.val+1) \ levels n.val) = D.core (v n)
    rw [level_before n.val n.isLt]
    by_cases before : n.val+1 < ℓ
    · rw [level_before (n.val+1) before]
      exact (chain_step n).2
    · rw [terminal (n.val+1) (by omega)]
      apply terminal_layer_core D (corePrefix D J v n.val)
        (chain n.castSucc).contains (chain n.castSucc).excludes
      · rintro (old | ⟨k, hk, same⟩)
        · exact fresh n old
        · have equal := injective same
          subst k
          exact (lt_irrefl n.val) hk
      · intro j
        rcases cover j with old | ⟨k, same⟩
        · exact Or.inl (Or.inl old)
        · by_cases earlier : k.val < n.val
          · exact Or.inl (Or.inr ⟨k, earlier, same⟩)
          · have equal : k = n := Fin.ext (by omega)
            exact Or.inr (same.symm.trans (congrArg v equal))
      · exact ordered n

theorem exists_full_source {ℓ : ℕ} (positive : 0 < ℓ)
    (v : Fin ℓ ≃ Fin D.count)
    (ordered : ∀ i j, D.edge (v i) (v j) → j < i) :
    ∃ S : AdaptedSource T ∅ D.core ℓ, S.index = v := by
  apply exists_source_from_trapping_base D isCompact_empty (fun _ hx => hx.elim) ∅
    (fun _ hj => hj.elim) (fun _ _ => disjoint_empty _) positive v v.injective
    (fun _ hj => hj.elim) (fun j => Or.inr (v.surjective j))
  intro i j edge
  obtain ⟨k, rfl⟩ := v.surjective j
  exact Or.inr ⟨k, ordered i k edge, rfl⟩

theorem exists_full_source_of_no_cycles (positive : 0 < D.count)
    (no_cycles : ∀ i, ¬ Relation.TransGen D.edge i i) :
    ∃ L : List (Fin D.count), L.Nodup ∧ (∀ j, j ∈ L) ∧
      (∀ i j : Fin L.length, D.edge (L.get i) (L.get j) → j < i) ∧
      ∃ S : AdaptedSource T ∅ D.core L.length, S.index = L.get := by
  classical
  let reverseEdge := Function.swap D.edge
  have acyclic (i : Fin D.count) : ¬ Relation.TransGen reverseEdge i i :=
    fun cycle => no_cycles i (Relation.transGen_swap.mp cycle)
  let wellFounded := PressureTopologicalOrder.wellFounded_of_acyclic reverseEdge acyclic
  let L := PressureTopologicalOrder.priorityOrder reverseEdge (fun _ => 0) wellFounded Finset.univ
  obtain ⟨cover, nodup, pairwise, length⟩ :=
    PressureTopologicalOrder.priorityOrder_spec reverseEdge (fun _ => 0) wellFounded Finset.univ
  have all (j : Fin D.count) : j ∈ L := (cover j).mpr (Finset.mem_univ _)
  have onto : Surjective L.get := fun j => List.mem_iff_get.mp (all j)
  let v : Fin L.length ≃ Fin D.count := Equiv.ofBijective L.get ⟨nodup.injective_get, onto⟩
  have ordered (i j : Fin L.length) (edge : D.edge (L.get i) (L.get j)) : j < i :=
    PressureTopologicalOrder.edge_indices wellFounded pairwise j i edge
  have nonempty : 0 < L.length := by
    have exactLength : L.length = D.count := by simpa only [Finset.card_univ, Fintype.card_fin] using length
    omega
  obtain ⟨S, index⟩ := exists_full_source D nonempty v ordered
  exact ⟨L, nodup, all, ordered, S, index⟩

end ConditionedStochasticStabilityHyperbolic.Global.FiniteBasicAdaptedFiltration
