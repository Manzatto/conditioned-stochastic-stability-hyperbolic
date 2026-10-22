module
public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry
public import LeanShared.Dynamics.NullBoundaryTrappingNeighborhood
public import LeanShared.Dynamics.TrappingSandwichCore

/-! Every finite adapted filtration has a null-boundary replacement with
the same absorbing base, indexing and literal isolated layer cores. -/
public noncomputable section
open Set MeasureTheory Metric
namespace ConditionedStochasticStabilityHyperbolic.Global.NullBoundaryAdaptedFiltration
open LeanShared ShiftedFiltrationGeometry
variable {X I : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_replacement (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
    (original : AdaptedSource T A Λ ℓ) (μ : Measure X) [SFinite μ] :
    ∃ repaired : AdaptedSource T A Λ ℓ,
      repaired.index = original.index ∧
      ∀ j, 0 < j → j ≤ ℓ → μ (frontier (repaired.levels j)) = 0 := by
  classical
  by_cases empty : ℓ = 0
  · refine ⟨original,rfl,?_⟩
    intro j positive bound
    omega
  have nonempty : 0 < ℓ := Nat.pos_of_ne_zero empty
  have neighborhoods (i : Fin ℓ) := NullBoundaryTrappingNeighborhood.exists_neighborhood T T.continuous μ
    (original.compact_positive (i.val+1) (by omega) (by omega))
    (original.adapted_positive (i.val+1) (by omega) (by omega))
    isOpen_univ (subset_univ _)
  choose q compact contains _ maps adapted boundary using neighborhoods
  let level (n : ℕ) : Set X :=
    if n=0 then A else ⋃ i ∈ ({i : Fin ℓ | i.val+1≤n} : Set (Fin ℓ)), q i
  have mem_level {n : ℕ} (positive : 0<n) {x : X} :
      x∈level n ↔ ∃ i : Fin ℓ, i.val+1≤n ∧ x∈q i := by
    simp only [level,Nat.ne_of_gt positive,ite_false,mem_iUnion,mem_ofPred_eq,exists_prop]
  have large {n : ℕ} (positive : 0<n) (bound : n≤ℓ) : original.levels n ⊆ interior (level n) := by
    let i : Fin ℓ := ⟨n-1,by omega⟩
    have same : i.val+1=n := by dsimp [i]; omega
    have subset : q i ⊆ level n := fun x hx => (mem_level positive).mpr ⟨i,by omega,hx⟩
    simpa only [same] using (contains i).trans (interior_mono subset)
  have small {n : ℕ} (positive : 0<n) {x : X} (hx:x∈level n) : T x∈interior (original.levels n) := by
    obtain ⟨i,hi,hx⟩ := (mem_level positive).mp hx
    exact interior_mono (original.monotone hi) (maps i hx)
  have sandwich {n : ℕ} (bound:n≤ℓ) :
      original.levels n ⊆ level n ∧ level n ⊆ T ⁻¹' original.levels n := by
    by_cases zero : n=0
    · subst n
      simpa only [level,ite_true,original.zero] using
        (show A⊆A ∧ A⊆T ⁻¹' A from ⟨Subset.rfl,original.absorbing_forward⟩)
    · exact ⟨(large (Nat.pos_of_ne_zero zero) bound).trans interior_subset,
        fun x hx => (show T x∈original.levels n from interior_subset (small (Nat.pos_of_ne_zero zero) hx))⟩
  have null {n : ℕ} (positive:0<n) : μ (frontier (level n))=0 := by
    have cover := (Set.toFinite ({i : Fin ℓ | i.val+1≤n} : Set (Fin ℓ))).frontier_biUnion_subset q
    apply measure_mono_null (show frontier (level n) ⊆ ⋃ i ∈ ({i : Fin ℓ | i.val+1≤n} : Set (Fin ℓ)), frontier (q i) from by
      simpa only [level,Nat.ne_of_gt positive,ite_false] using cover)
    exact measure_iUnion_null fun i => measure_iUnion_null fun _ => boundary i
  let repaired : AdaptedSource T A Λ ℓ := {
    levels := level
    index := original.index
    zero := by simp only [level,ite_true]
    monotone := by
      intro m n hmn x hx
      by_cases zero : m=0
      · subst m
        by_cases zeroN : n=0
        · simpa only [zeroN] using hx
        · have hA : x∈A := by simpa only [level,ite_true] using hx
          let i : Fin ℓ := ⟨0,nonempty⟩
          apply (mem_level (Nat.pos_of_ne_zero zeroN)).mpr
          refine ⟨i,by dsimp [i]; omega,?_⟩
          exact interior_subset (contains i (original.monotone (Nat.zero_le _) (original.zero.symm ▸ hA)))
      · obtain ⟨i,hi,hx⟩ := (mem_level (Nat.pos_of_ne_zero zero)).mp hx
        exact (mem_level (by omega)).mpr ⟨i,hi.trans hmn,hx⟩
    absorbing_forward := original.absorbing_forward
    compact_positive := by
      intro n positive _
      dsimp only [level]
      rw [ite_eq_right (Nat.ne_of_gt positive)]
      exact (Set.toFinite _).isCompact_biUnion fun i _ => compact i
    adapted_positive := by
      intro n positive bound x hx
      exact interior_mono (sandwich bound).1 (small positive hx)
    terminal := by
      apply eq_univ_of_forall
      intro x
      exact (sandwich (le_refl ℓ)).1 (original.terminal.symm ▸ mem_univ x)
    literal_core := by
      intro i
      have h := TrappingSandwichCore.layer T
        (sandwich (show i.val+1≤ℓ by omega)).1 (sandwich (show i.val+1≤ℓ by omega)).2
        (sandwich (show i.val≤ℓ by omega)).1 (sandwich (show i.val≤ℓ by omega)).2
      exact h.trans (original.literal_core i)
  }
  exact ⟨repaired,rfl,fun _ positive _ => null positive⟩

/-- The same replacement can make the product boundaries null for an
arbitrary finite joint reference measure; product-measure structure is
unnecessary. Its first marginal selects the distance levels. -/
theorem exists_product_null_replacement {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace (X × Y)] [BorelSpace (X × Y)]
    (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
    (original : AdaptedSource T A Λ ℓ) (μ : Measure (X × Y)) [IsFiniteMeasure μ] :
    ∃ repaired : AdaptedSource T A Λ ℓ,
      repaired.index = original.index ∧
      ∀ j, 0 < j → j ≤ ℓ → μ (frontier (repaired.levels j ×ˢ (univ : Set Y))) = 0 := by
  obtain ⟨repaired,index,boundary⟩ := exists_replacement T A Λ ℓ original (μ.map Prod.fst)
  refine ⟨repaired,index,?_⟩
  intro j positive bound
  have null := boundary j positive bound
  rw [Measure.map_apply continuous_fst.measurable isClosed_frontier.measurableSet] at null
  rw [frontier_prod_univ_eq]
  simpa only [prod_univ] using null
end ConditionedStochasticStabilityHyperbolic.Global.NullBoundaryAdaptedFiltration
