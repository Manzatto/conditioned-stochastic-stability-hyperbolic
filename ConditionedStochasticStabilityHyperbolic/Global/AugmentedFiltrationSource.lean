module

public import LeanShared.Dynamics.AbsorbingBaseReplacement
public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry

/-! # Fixed absorbing base derived from an ordinary full adapted filtration

A standard full filtration starts at the empty set and has one initial
absorbing attractor layer. Expand its positive levels by a common inverse
iterate, discard that first layer, and use the actual A as level zero. Only
finite deterministic absorption and A containment enter this proved
deduction; no relative augmented-filtration theorem is assumed.
-/
@[expose] public noncomputable section
open Set Function
namespace ConditionedStochasticStabilityHyperbolic.Global.AugmentedFiltrationSource
open LeanShared ShiftedFiltrationGeometry
variable {X I : Type*} [MetricSpace X]
  (T : X ≃ₜ X) (Γ : I → Set X) (ℓ L : ℕ)
  (D : AdaptedSource T ∅ Γ (ℓ + 1))

def retainedSets : Fin ℓ → Set X := fun i => Γ (D.index ⟨i.val + 1, by omega⟩)

def augmentedLevels (A : Set X) : ℕ → Set X :=
  fun j => if j = 0 then A else levels T ∅ Γ (ℓ + 1) L D (j + 1)

/-- Actual fixed-A augmented source is constructed from the standard full
filtration. The former first level is eliminated by finite absorption. -/
def actualSource (A : Set X) (hℓ : 0 < ℓ) (hAfwd : MapsTo T A A)
    (hcontain : A ⊆ levels T ∅ Γ (ℓ + 1) L D 2)
    (N : ℕ) (habsorb : MapsTo ((T : X → X)^[N]) (levels T ∅ Γ (ℓ + 1) L D 1) A)
    (hfirst : retainedSets T Γ ℓ D ⟨0, hℓ⟩ ⊆ Aᶜ) :
    AdaptedSource T A (retainedSets T Γ ℓ D) ℓ where
  levels := augmentedLevels T Γ ℓ L D A
  index := id
  zero := by simp [augmentedLevels]
  monotone := by
    intro i j hij x hx
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j; exact hx
      · simp only [augmentedLevels] at hx
        simp only [augmentedLevels, ite_eq_right hj]
        exact levels_monotone T ∅ Γ (ℓ + 1) L D (by omega : 2 ≤ j + 1) (hcontain hx)
    · have hj : j ≠ 0 := by omega
      simp only [augmentedLevels, ite_eq_right hi] at hx
      simp only [augmentedLevels, ite_eq_right hj]
      exact levels_monotone T ∅ Γ (ℓ + 1) L D (Nat.add_le_add_right hij 1) hx
  absorbing_forward := hAfwd
  compact_positive := by
    intro i hi hiℓ
    simp only [augmentedLevels, ite_eq_right (Nat.ne_of_gt hi)]
    exact levels_positive_compact T ∅ Γ (ℓ + 1) L D (i + 1) (by omega) (by omega)
  adapted_positive := by
    intro i hi hiℓ
    simp only [augmentedLevels, ite_eq_right (Nat.ne_of_gt hi)]
    exact levels_positive_adapted T ∅ Γ (ℓ + 1) L D (i + 1) (by omega) (by omega)
  terminal := by
    simp only [augmentedLevels, ite_eq_right (Nat.ne_of_gt hℓ)]
    rw [levels, shiftedFiltration_pos T L ∅ D.levels (by omega), D.terminal, preimage_univ]
  literal_core := by
    intro i
    have hcore := ShiftedFiltrationGeometry.literal_core T ∅ Γ (ℓ + 1) L D
      ⟨i.val + 1, by omega⟩
    change isolatedCore T (filtrationLayer (augmentedLevels T Γ ℓ L D A) i.val) =
      Γ (D.index ⟨i.val + 1, by omega⟩)
    by_cases hi : i.val = 0
    · have hcore0 : isolatedCore T (levels T ∅ Γ (ℓ + 1) L D 2 \ levels T ∅ Γ (ℓ + 1) L D 1) =
          retainedSets T Γ ℓ D ⟨0, hℓ⟩ := by
        simpa only [hi, filtrationLayer, zero_add, Nat.reduceAdd, retainedSets] using hcore
      have heq := isolatedCore_replace_absorbing_base T (levels T ∅ Γ (ℓ + 1) L D 2)
        A (levels T ∅ Γ (ℓ + 1) L D 1) (fun y hy => ⟨N, habsorb hy⟩) (by
          apply Set.disjoint_left.mpr
          intro x hx ha
          exact hfirst (hcore0 ▸ hx) ha)
      change isolatedCore T (filtrationLayer (augmentedLevels T Γ ℓ L D A) i.val) = _
      simp only [hi, filtrationLayer, zero_add, augmentedLevels, ite_eq_right (by omega : (1 : ℕ) ≠ 0)]
      exact heq.trans (by simpa only [hi, filtrationLayer, zero_add, Nat.reduceAdd] using hcore)
    · simp only [filtrationLayer, augmentedLevels, ite_eq_right (by omega : i.val + 1 ≠ 0), ite_eq_right hi]
      exact hcore

private theorem forwardTrapped_eq_of_forward_invariant (K : Set X) (hK : MapsTo T K K) :
    forwardTrapped T K = K := by
  apply Subset.antisymm (forwardTrapped_subset T K)
  intro x hx n
  exact hK.iterate n hx

/-- The needed shift and finite absorption bounds are derived from strict
trapping, compactness and the actual absorbing-attractor core identification. -/
theorem exists_actualSource [CompactSpace X] (A : Set X) (hA : IsOpen A)
    (hℓ : 0 < ℓ) (hstrict : MapsTo T (closure A) A)
    (hattr : isolatedCore T (D.levels 1) = isolatedCore T (closure A))
    (hfirst : retainedSets T Γ ℓ D ⟨0, hℓ⟩ ⊆ Aᶜ) :
    ∃ L : ℕ, 0 < L ∧ ∃ E : AdaptedSource T A (retainedSets T Γ ℓ D) ℓ,
      E.index = id ∧ ∀ j : ℕ, 0 < j →
        E.levels j = (T : X → X)^[L] ⁻¹' D.levels (j + 1) := by
  have hAfwd : MapsTo T A A := fun _ hx => hstrict (subset_closure hx)
  have hAclosure : MapsTo T (closure A) (closure A) := fun _ hx => subset_closure (hstrict hx)
  have hC1fwd : MapsTo T (D.levels 1) (D.levels 1) :=
    fun _ hx => interior_subset (D.adapted_positive 1 (by omega) (by omega) hx)
  have hcoreA : isolatedCore T (closure A) ⊆ A := by
    intro x hx
    have hp := hstrict (hx.2 1)
    simpa only [iterate_one, T.apply_symm_apply] using hp
  obtain ⟨N, hN, hNtail⟩ := exists_pos_stable_tail_subset T
    (D.compact_positive 1 (by omega) (by omega)) hA (hattr ▸ hcoreA)
  rw [forwardTrapped_eq_of_forward_invariant T (D.levels 1) hC1fwd] at hNtail
  have hcore2 : isolatedCore T (closure A) ⊆ interior (D.levels 2) := by
    intro x hx
    have hxC1 : x ∈ isolatedCore T (D.levels 1) := hattr.symm ▸ hx
    have hp := D.adapted_positive 2 (by omega) (by omega)
      (D.monotone (by omega : 1 ≤ 2) (hxC1.2 1))
    simpa only [iterate_one, T.apply_symm_apply] using hp
  obtain ⟨L, hL, hLtail⟩ := exists_pos_stable_tail_subset T isClosed_closure.isCompact
    isOpen_interior hcore2
  rw [forwardTrapped_eq_of_forward_invariant T (closure A) hAclosure] at hLtail
  have hcontain : A ⊆ levels T ∅ Γ (ℓ + 1) L D 2 := by
    intro x hx
    rw [levels, shiftedFiltration_pos T L ∅ D.levels (by omega)]
    change (T : X → X)^[L] x ∈ D.levels 2
    exact interior_subset (hLtail ⟨x, subset_closure hx, rfl⟩)
  have habsorb : MapsTo ((T : X → X)^[N + L]) (levels T ∅ Γ (ℓ + 1) L D 1) A := by
    intro x hx
    rw [levels, shiftedFiltration_pos T L ∅ D.levels (by omega)] at hx
    rw [iterate_add_apply]
    exact hNtail ⟨(T : X → X)^[L] x, hx, rfl⟩
  refine ⟨L, hL, actualSource T Γ ℓ L D A hℓ hAfwd hcontain (N + L) habsorb hfirst, rfl, ?_⟩
  intro j hj
  change augmentedLevels T Γ ℓ L D A j = _
  simp only [augmentedLevels, ite_eq_right (Nat.ne_of_gt hj), levels,
    shiftedFiltration_pos T L ∅ D.levels (by omega : 0 < j + 1)]

end ConditionedStochasticStabilityHyperbolic.Global.AugmentedFiltrationSource
