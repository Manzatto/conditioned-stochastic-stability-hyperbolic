module

public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry

/-!
# A stable starting state lies inside a common shifted positive prefix

Basic sets are proved compact from their actual closed isolating layers.
Their derived interior property gives a uniform neighborhood. Ordinary stable
orbit approach then chooses a positive finite preimage shift containing the
starting state, while the absorbing region remains fixed.
-/

@[expose] public section
open Set Function Metric
namespace ConditionedStochasticStabilityHyperbolic.Global.StableShiftEntry
open LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry
variable {X I : Type*} [MetricSpace X]

/-- Every actual closed analytic layer is compact, as a closed subset of
its compact upper positive filtration level. -/
theorem closed_layer_compact
    (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (i : Fin ℓ) :
    IsCompact (closure (filtrationLayer (levels T A Λ ℓ N D) i.val)) := by
  have hK := levels_positive_compact T A Λ ℓ N D (i.val + 1) (by omega) (by omega)
  apply hK.of_isClosed_subset isClosed_closure
  exact (closure_stratum_subset _ _ hK.isClosed).trans inter_subset_left

/-- The classical literal core identification and proved closed-layer
geometry imply compactness of every retained basic set. -/
theorem basic_set_compact
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (i : Fin ℓ) : IsCompact (Λ (D.index i)) := by
  rw [← closed_layer_core T A Λ ℓ N D hA i]
  have hK := closed_layer_compact T A Λ ℓ N D i
  exact (isCompact_forwardTrapped T.continuous hK).inter_right
    (isClosed_forwardTrapped T.symm.continuous hK.isClosed)

/-- Stable-orbit approach gives a positive common preimage shift containing
the initial state in the intended positive prefix's interior. -/
theorem exists_shift_containing_stable_start
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
    (D : AdaptedSource T A Λ ℓ) (hsep : ∀ j, Λ j ⊆ interior Aᶜ)
    (i : Fin ℓ) (x : X)
    (happroach : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index i),
      dist ((T : X → X)^[n + 1] x) y < r) :
    ∃ N : ℕ, 0 < N ∧ x ∈ interior (levels T A Λ ℓ N D (i.val + 1)) := by
  have hcompact := basic_set_compact T A hA Λ ℓ 0 D i
  have hcoreint := basic_set_interior_stratum T A Λ ℓ 0 D hsep i
  have hupper : Λ (D.index i) ⊆ interior (levels T A Λ ℓ 0 D (i.val + 1)) :=
    hcoreint.trans (interior_mono sdiff_subset)
  obtain ⟨r, hr, hthick⟩ := hcompact.exists_thickening_subset_open isOpen_interior hupper
  obtain ⟨n, y, hy, hnear⟩ := happroach r hr
  have hent : (T : X → X)^[n + 1] x ∈ interior (D.levels (i.val + 1)) := by
    have ht := hthick (mem_thickening_iff.mpr ⟨y, hy, hnear⟩)
    simpa only [levels, shiftedFiltration_pos T 0 A D.levels (Nat.succ_pos i.val),
      iterate_zero, preimage_id] using ht
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [levels, shiftedFiltration_pos T (n + 1) A D.levels (Nat.succ_pos i.val),
    ← preimage_iterate_interior]
  exact hent

end ConditionedStochasticStabilityHyperbolic.Global.StableShiftEntry
