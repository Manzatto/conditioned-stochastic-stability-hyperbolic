module
public import ConditionedStochasticStabilityHyperbolic.Global.NonwanderingOrbitCapture

/-! A finite disjoint compact invariant decomposition of the actual
nonwandering set determines the asymptotic basic set of every orbit. -/
public noncomputable section
open Set Filter Function Metric
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.FiniteNonwanderingBasins
variable {X I : Type*} [MetricSpace X] [CompactSpace X] [Fintype I]

theorem exists_stable_basic (T : X → X) (continuous : Continuous T) (Λ : I → Set X)
    (compact : ∀ i, IsCompact (Λ i)) (nonempty : ∀ i, (Λ i).Nonempty)
    (disjoint : Pairwise (fun i j => Disjoint (Λ i) (Λ j)))
    (forward : ∀ i, MapsTo T (Λ i) (Λ i))
    (cover : Paper.nonwanderingSet T ⊆ ⋃ i, Λ i) (x : X) :
    ∃ i, x∈PaperStableBasin.stableBasin T (Λ i) := by
  classical
  let U (i : I) : Set X := ⋂ j, {y : X | i=j ∨ infDist y (Λ i) < infDist y (Λ j)}
  have openU (i : I) : IsOpen (U i) := by
    apply isOpen_iInter_of_finite
    intro j
    by_cases same : i=j
    · simp only [same,true_or,ofPred_true]
      exact isOpen_univ
    · simpa only [same,false_or] using isOpen_lt (continuous_infDist_pt _) (continuous_infDist_pt _)
  have insideU (i : I) : Λ i ⊆ U i := by
    intro y hy
    apply mem_iInter.mpr
    intro j
    by_cases same : i=j
    · exact Or.inl same
    · apply Or.inr
      rw [infDist_zero_of_mem hy]
      apply (compact j).isClosed.notMem_iff_infDist_pos (nonempty j) |>.mp
      exact fun hj => Set.disjoint_left.mp (disjoint same) hy hj
  have disjointU : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j different
    apply Set.disjoint_left.mpr
    intro y hi hj
    have a := (mem_iInter.mp hi j).resolve_left different
    have b := (mem_iInter.mp hj i).resolve_left different.symm
    exact (lt_asymm a b)
  let V (i : I) := U i ∩ T ⁻¹' U i
  have openV (i : I) : IsOpen (V i) := (openU i).inter ((openU i).preimage continuous)
  have coreV (i : I) : Λ i ⊆ V i := fun y hy => ⟨insideU i hy,insideU i (forward i hy)⟩
  have covered : Paper.nonwanderingSet T ⊆ ⋃ i, V i := by
    intro y hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp (cover hy)
    exact mem_iUnion.mpr ⟨i,coreV i hi⟩
  obtain ⟨N,capture⟩ := eventually_atTop.mp
    (NonwanderingOrbitCapture.eventually_in_neighborhood T (isOpen_iUnion openV) covered x)
  obtain ⟨i,initial⟩ := mem_iUnion.mp (capture N (le_refl _))
  have stays (k : ℕ) : T^[N+k] x∈V i := by
    induction k with
    | zero => simpa only [Nat.add_zero] using initial
    | succ k ih =>
      have hit : T^[N+(k+1)] x∈U i := by
        rw [Nat.add_succ,iterate_succ_apply']
        exact ih.2
      obtain ⟨j,hj⟩ := mem_iUnion.mp (capture (N+(k+1)) (Nat.le_add_right _ _))
      have same : i=j := by
        by_contra different
        exact Set.disjoint_left.mp (disjointU different) hit hj.1
      exact same.symm ▸ hj
  refine ⟨i,nonempty i,?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε positive
  let O := thickening ε (Λ i) ∪ ⋃ j ∈ ({j : I | j≠i} : Set I), U j
  have openO : IsOpen O := isOpen_thickening.union (isOpen_iUnion fun j => isOpen_iUnion fun _ => openU j)
  have coverO : Paper.nonwanderingSet T ⊆ O := by
    intro y hy
    obtain ⟨j,hj⟩ := mem_iUnion.mp (cover hy)
    by_cases same : j=i
    · exact Or.inl (self_subset_thickening positive _ (same ▸ hj))
    · exact Or.inr (mem_iUnion₂.mpr ⟨j,same,insideU j hj⟩)
  filter_upwards [NonwanderingOrbitCapture.eventually_in_neighborhood T openO coverO x,
    eventually_ge_atTop N] with n hn bound
  have inU : T^[n] x∈U i := by
    have h := (stays (n-N)).1
    simpa only [Nat.add_sub_of_le bound] using h
  have close : T^[n] x∈thickening ε (Λ i) := by
    rcases hn with close | other
    · exact close
    · obtain ⟨j,different,hit⟩ := mem_iUnion₂.mp other
      exact False.elim (Set.disjoint_left.mp (disjointU different.symm) inU hit)
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg infDist_nonneg] using
    (mem_thickening_iff_infDist_lt (nonempty i)).mp close
end ConditionedStochasticStabilityHyperbolic.Global.FiniteNonwanderingBasins
