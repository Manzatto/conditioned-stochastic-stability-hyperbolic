module

public import ConditionedStochasticStabilityHyperbolic.Global.BasicSetSinkTrapping
public import LeanShared.Dynamics.CompactForwardTube
public import Mathlib.Topology.Separation.Regular

/-! Constructive extension of a compact strict trapping level by the next
basic set in a sink-first order. The first-exit set of its isolated collar
has a uniform finite entrance time into the previous level. -/

public noncomputable section
open Set Function Bundle Metric Filter
open scoped Topology Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Global.BasicSetFiltrationStep

section Basin
variable {X : Type*} [MetricSpace X]

theorem stableBasin_eventually_in_open (T : X → X) {Γ O : Set X}
    (compact : IsCompact Γ) (openO : IsOpen O) (contains : Γ ⊆ O)
    {x : X} (basin : x ∈ PaperStableBasin.stableBasin T Γ) :
    ∀ᶠ n : ℕ in atTop, T^[n] x ∈ O := by
  obtain ⟨δ, positive, inside⟩ := compact.exists_thickening_subset_open openO contains
  filter_upwards [basin.2.eventually (gt_mem_nhds positive)] with n hn
  exact inside ((mem_thickening_iff_infDist_lt basin.1).mpr hn)

theorem stableBasin_enters_open (T : X → X) {Γ O : Set X}
    (compact : IsCompact Γ) (openO : IsOpen O) (contains : Γ ⊆ O)
    {x : X} (basin : x ∈ PaperStableBasin.stableBasin T Γ) :
    ∃ n : ℕ, T^[n] x ∈ O :=
  (stableBasin_eventually_in_open T compact openO contains basin).exists

theorem unstableBasin_forward (T : X ≃ₜ X) (Γ : Set X) :
    MapsTo T (PaperStableBasin.unstableBasin T Γ)
      (PaperStableBasin.unstableBasin T Γ) := by
  intro x hx
  refine ⟨hx.1, (tendsto_add_atTop_iff_nat 1).mp ?_⟩
  simpa only [iterate_succ_apply, T.symm_apply_apply] using hx.2

theorem unstableBasin_subset_forward_invariant (T : X ≃ₜ X)
    {Γ C : Set X} (compact : IsCompact Γ) (contains : Γ ⊆ interior C)
    (forward : MapsTo T C C) : PaperStableBasin.unstableBasin T Γ ⊆ C := by
  intro x basin
  obtain ⟨n, captured⟩ := stableBasin_enters_open T.symm compact isOpen_interior contains basin
  have back : T^[n] (T.symm^[n] x) ∈ C := forward.iterate n (interior_subset captured)
  have cancel : T^[n] (T.symm^[n] x) = x := T.right_inv.iterate n x
  exact cancel ▸ back

theorem forwardTrapped_excludes_basin (T : X → X) (continuous : Continuous T)
    {K Γ : Set X} (compactK : IsCompact K) (compactΓ : IsCompact Γ)
    (disjoint : Disjoint Γ K) :
    Disjoint (LeanShared.forwardTrapped T K) (PaperStableBasin.stableBasin T Γ) :=
  BasicSetSinkGeometry.invariant_excludes_basin T compactΓ
    (LeanShared.isClosed_forwardTrapped continuous compactK.isClosed)
    (disjoint.mono_right (LeanShared.forwardTrapped_subset T K))
    (LeanShared.mapsTo_forwardTrapped T K)

end Basin

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} (D : Paper.SpectralDecomposition (E := E) T)

omit [CompactSpace M] in
theorem core_disjoint_other_unstable {i j : Fin D.count} (different : i ≠ j) :
    Disjoint (D.core j) (PaperStableBasin.unstableBasin T (D.core i)) := by
  apply BasicSetSinkGeometry.invariant_excludes_basin T.symm
    (D.basic i).hyperbolic.compact (D.basic j).hyperbolic.compact.isClosed (D.disjoint different)
  intro x hx
  obtain ⟨y, hy, same⟩ := (D.basic j).hyperbolic.invariant.symm ▸ hx
  simpa only [← same, T.symm_apply_apply] using hy

theorem isCompact_union_unstableBasin {C : Set M} (compactC : IsCompact C)
    (trapping : MapsTo T C (interior C)) {i : Fin D.count}
    (targets : ∀ j, D.edge i j → D.core j ⊆ interior C) :
    IsCompact (C ∪ PaperStableBasin.unstableBasin T (D.core i)) := by
  let K := closure (D.collar i)
  let P := LeanShared.forwardTrapped T.symm K
  let B := T '' P \ interior K
  have compactK : IsCompact K := isClosed_closure.isCompact
  have compactP : IsCompact P := LeanShared.isCompact_forwardTrapped T.symm.continuous compactK
  have compactB : IsCompact B := (compactP.image T.continuous).diff isOpen_interior
  have coreInside : D.core i ⊆ interior K := (D.basic i).subset_neighborhood.trans
    (interior_maximal subset_closure (D.basic i).open_neighborhood)
  have coreEq : LeanShared.isolatedCore T.symm K = D.core i := by
    rw [(D.basic i).isolated]
    exact Set.inter_comm _ _
  have past : P ⊆ PaperStableBasin.unstableBasin T (D.core i) := by
    have h := BasicSetSinkTrapping.forwardTrapped_subset_stableBasin T.symm compactK
      (coreEq.symm ▸ (D.basic i).nonempty)
    simpa only [PaperStableBasin.unstableBasin, coreEq] using h
  have exitPast : B ⊆ PaperStableBasin.unstableBasin T (D.core i) := by
    rintro x ⟨⟨y, hy, rfl⟩, _⟩
    exact unstableBasin_forward T _ (past hy)
  have enters : ∀ x ∈ B, ∃ n : ℕ, T^[n] x ∈ interior C := by
    intro x hx
    obtain ⟨j, future⟩ := BasicSetBasinDecomposition.forward D x
    have outsideI : x ∉ D.core i := fun member => hx.2 (coreInside member)
    have outsideJ : x ∉ D.core j := by
      by_cases same : i = j
      · exact same ▸ outsideI
      · exact fun member => Set.disjoint_left.mp
          (core_disjoint_other_unstable D same) member (exitPast hx)
    have edge : D.edge i j := ⟨x, ⟨exitPast hx, outsideI⟩, ⟨future, outsideJ⟩⟩
    exact stableBasin_enters_open T (D.basic j).hyperbolic.compact isOpen_interior
      (targets j edge) future
  obtain ⟨N, capture⟩ := LeanShared.CompactForwardTube.exists_uniform_entrance T T.continuous
    compactB isOpen_interior (fun _ hx => trapping (interior_subset hx)) enters
  have exit : MapsTo T P (P ∪ B) := by
    intro x hx
    by_cases inside : T x ∈ interior K
    · apply Or.inl
      exact LeanShared.mem_forwardTrapped_of_mem_of_image_mem (interior_subset inside)
        (by simpa only [T.symm_apply_apply] using hx)
    · exact Or.inr ⟨⟨x, hx, rfl⟩, inside⟩
  obtain ⟨H, compactH, contains, forward, upper⟩ :=
    LeanShared.CompactForwardTube.exists_compact_saturation T T.continuous compactC compactP
      compactB (fun _ hx => interior_subset (trapping hx)) exit
      (fun _ hx => interior_subset (capture hx))
  have equality : H = C ∪ PaperStableBasin.unstableBasin T (D.core i) := by
    apply Subset.antisymm
    · intro x hx
      rcases upper hx with inC | tube
      · exact Or.inl inC
      · obtain ⟨n, hn⟩ := mem_iUnion.mp tube
        rcases hn with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
        · exact Or.inr ((unstableBasin_forward T _).iterate n (past hy))
        · exact Or.inr ((unstableBasin_forward T _).iterate n (exitPast hy))
    · intro x hx
      rcases hx with inC | basin
      · exact contains (Or.inl inC)
      · obtain ⟨n, tail⟩ := eventually_atTop.mp (stableBasin_eventually_in_open T.symm
          (D.basic i).hyperbolic.compact (D.basic i).open_neighborhood
          (D.basic i).subset_neighborhood basin)
        have pastTail : T.symm^[n] x ∈ P := by
          intro m
          rw [← iterate_add_apply]
          exact subset_closure (tail (m+n) (Nat.le_add_left _ _))
        have h := forward.iterate n (contains (Or.inr pastTail))
        have cancel : T^[n] (T.symm^[n] x) = x := T.right_inv.iterate n x
        exact cancel ▸ h
  exact equality ▸ compactH

theorem exists_next_level {C : Set M} (compactC : IsCompact C)
    (trapping : MapsTo T C (interior C)) (J : Set (Fin D.count))
    (contains : ∀ j ∈ J, D.core j ⊆ interior C)
    (excludes : ∀ j ∉ J, Disjoint (D.core j) C)
    {i : Fin D.count} (fresh : i ∉ J)
    (targets : ∀ j, D.edge i j → j ∈ J) :
    ∃ C' : Set M, IsCompact C' ∧ C ⊆ C' ∧ MapsTo T C' (interior C') ∧
      (∀ j ∈ insert i J, D.core j ⊆ interior C') ∧
      (∀ j ∉ insert i J, Disjoint (D.core j) C') ∧
      LeanShared.isolatedCore T (C' \ C) = D.core i := by
  let H := C ∪ PaperStableBasin.unstableBasin T (D.core i)
  have compactH : IsCompact H := isCompact_union_unstableBasin D compactC trapping
    (fun j edge => contains j (targets j edge))
  have forwardC : MapsTo T C C := fun _ hx => interior_subset (trapping hx)
  have forwardH : MapsTo T H H := by
    intro x hx
    exact hx.elim (fun h => Or.inl (forwardC h))
      (fun h => Or.inr (unstableBasin_forward T _ h))
  let O := (⋃ j ∉ insert i J, D.core j)ᶜ
  have openO : IsOpen O :=
    (isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite
      fun _ => (D.basic j).hyperbolic.compact.isClosed).isOpen_compl
  have insideO : H ⊆ O := by
    intro x hx outside
    obtain ⟨j, hj, member⟩ := mem_iUnion₂.mp outside
    have different : i ≠ j := fun same => hj (mem_insert_iff.mpr (Or.inl same.symm))
    rcases hx with inC | basin
    · exact Set.disjoint_left.mp (excludes j (fun h => hj (mem_insert_of_mem i h))) member inC
    · exact Set.disjoint_left.mp (core_disjoint_other_unstable D different) member basin
  obtain ⟨V, openV, containsV, closureV⟩ :=
    compactH.exists_isOpen_closure_subset (openO.mem_nhdsSet.mpr insideO)
  let K := closure V
  have compactK : IsCompact K := isClosed_closure.isCompact
  have insideK : H ⊆ interior K := containsV.trans (interior_maximal subset_closure openV)
  have excludesK (j : Fin D.count) (hj : j ∉ insert i J) : Disjoint (D.core j) K := by
    apply Set.disjoint_left.mpr
    intro x core member
    exact closureV member (mem_iUnion₂.mpr ⟨j, hj, core⟩)
  have pastH : LeanShared.forwardTrapped T.symm K ⊆ H := by
    intro x hx
    obtain ⟨j, basin⟩ := BasicSetBasinDecomposition.backward D x
    by_cases old : j ∈ J
    · exact Or.inl (unstableBasin_subset_forward_invariant T
        (D.basic j).hyperbolic.compact (contains j old) forwardC basin)
    by_cases same : j = i
    · exact Or.inr (same ▸ basin)
    · have excluded : j ∉ insert i J := by simpa only [mem_insert_iff, not_or] using ⟨same, old⟩
      exact False.elim (Set.disjoint_left.mp
        (forwardTrapped_excludes_basin T.symm T.symm.continuous compactK
          (D.basic j).hyperbolic.compact (excludesK j excluded)) hx basin)
  have noExternal : LeanShared.forwardTrapped T.symm K ⊆ LeanShared.isolatedCore T K := by
    intro x hx
    exact ⟨fun n => interior_subset (insideK (forwardH.iterate n (pastH hx))), hx⟩
  have coreInside : LeanShared.isolatedCore T K ⊆ interior K :=
    fun _ hx => insideK (pastH hx.2)
  have corePast : D.core i ⊆ PaperStableBasin.unstableBasin T (D.core i) := by
    intro x hx
    have past := ((D.basic i).isolated ▸ hx).2
    have coreEq : LeanShared.isolatedCore T.symm (closure (D.collar i)) = D.core i := by
      rw [(D.basic i).isolated]
      exact Set.inter_comm _ _
    have basin := BasicSetSinkTrapping.forwardTrapped_subset_stableBasin T.symm
      isClosed_closure.isCompact (coreEq.symm ▸ (D.basic i).nonempty) past
    simpa only [PaperStableBasin.unstableBasin, coreEq] using basin
  have coreK : D.core i ⊆ LeanShared.isolatedCore T K := by
    intro x hx
    have original := (D.basic i).isolated ▸ hx
    refine ⟨fun n => ?_, fun n => ?_⟩
    · have member := LeanShared.iterate_mem_isolatedCore T _ original n
      rw [← (D.basic i).isolated] at member
      exact interior_subset (insideK (Or.inr (corePast member)))
    · have member := LeanShared.iterate_symm_mem_isolatedCore T _ original n
      rw [← (D.basic i).isolated] at member
      exact interior_subset (insideK (Or.inr (corePast member)))
  have nonemptyK : K.Nonempty := (D.basic i).nonempty.mono
    (fun _ hx => (coreK hx).1 0)
  obtain ⟨S, compactS, coreS, insideS, trappingS, _sameCore⟩ :=
    LeanShared.CompactPastTrappingNeighborhood.exists_neighborhood T compactK nonemptyK
      coreInside noExternal openO (fun _ hx => insideO (pastH hx.2))
  let C' := C ∪ S
  have containsC : C ⊆ C' := subset_union_left
  have oldInside : interior C ⊆ interior C' := interior_mono containsC
  have newInside : interior S ⊆ interior C' := interior_mono subset_union_right
  have contains' (j : Fin D.count) (hj : j ∈ insert i J) : D.core j ⊆ interior C' := by
    rcases mem_insert_iff.mp hj with rfl | old
    · exact fun _ hx => newInside (coreS (coreK hx))
    · exact (contains j old).trans oldInside
  have insideO' : C' ⊆ O := by
    intro x hx
    exact hx.elim (fun h => insideO (Or.inl h)) (fun h => (insideS h).1)
  have excludes' (j : Fin D.count) (hj : j ∉ insert i J) : Disjoint (D.core j) C' := by
    apply Set.disjoint_left.mpr
    exact fun x core member => insideO' member (mem_iUnion₂.mpr ⟨j, hj, core⟩)
  have trapping' : MapsTo T C' (interior C') := by
    intro x hx
    exact hx.elim (fun h => oldInside (trapping h)) (fun h => newInside (trappingS h))
  refine ⟨C', compactC.union compactS, containsC, trapping', contains', excludes', ?_⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j, past⟩ := BasicSetBasinDecomposition.backward D x
    obtain ⟨k, future⟩ := BasicSetBasinDecomposition.forward D x
    have classify (R : M ≃ₜ M) (j : Fin D.count)
        (trapped : x ∈ LeanShared.forwardTrapped R (C' \ C))
        (basin : x ∈ PaperStableBasin.stableBasin R (D.core j)) : j = i := by
      by_cases old : j ∈ J
      · obtain ⟨n, hit⟩ := stableBasin_enters_open R (D.basic j).hyperbolic.compact
          isOpen_interior (contains j old) basin
        exact False.elim ((trapped n).2 (interior_subset hit))
      by_contra different
      have outside : j ∉ insert i J := by
        simpa only [mem_insert_iff, not_or] using ⟨different, old⟩
      exact Set.disjoint_left.mp (forwardTrapped_excludes_basin R R.continuous
        (compactC.union compactS) (D.basic j).hyperbolic.compact (excludes' j outside))
        (fun n => (trapped n).1) basin
    have pastSame : j = i := classify T.symm j hx.2 past
    have futureSame : k = i := classify T k hx.1 future
    subst j
    subst k
    by_contra outside
    exact fresh (targets i ⟨x, ⟨past, outside⟩, ⟨future, outside⟩⟩)
  · intro x hx
    have member (y : M) (hy : y ∈ D.core i) : y ∈ C' \ C :=
      ⟨interior_subset (contains' i (mem_insert i J) hy),
        fun hc => Set.disjoint_left.mp (excludes i fresh) hy hc⟩
    have original := (D.basic i).isolated ▸ hx
    refine ⟨fun n => member _ ?_, fun n => member _ ?_⟩
    · simpa only [← (D.basic i).isolated] using LeanShared.iterate_mem_isolatedCore T _ original n
    · simpa only [← (D.basic i).isolated] using LeanShared.iterate_symm_mem_isolatedCore T _ original n

end ConditionedStochasticStabilityHyperbolic.Global.BasicSetFiltrationStep
