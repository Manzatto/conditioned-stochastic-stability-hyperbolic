module

public import ConditionedStochasticStabilityHyperbolic.Global.StableShiftEntry
public import ConditionedStochasticStabilityHyperbolic.Global.ActualBasinGeometry

/-! # Actual stable starts enter a shifted selected prefix

A deterministic stable starting state need not belong to the original prefix.
A single finite preimage shift places it in the chosen pressure block's prefix;
strict trapping then proves that its entire forward orbit is live. This is the
geometric source of the starting-state-dependent noise tolerance.
-/
@[expose] public section
open Set Function Metric
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualStablePrefixEntry
open LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry ActualBasinGeometry
variable {X I : Type*} [MetricSpace X]

theorem exists_actual_shifted_prefix_for_stable_start
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A)
    (hstrict : MapsTo T (closure A) A) (Λ : I → Set X) (ℓ : ℕ)
    (D : AdaptedSource T A Λ ℓ) (hsep : ∀ j, Λ j ⊆ interior Aᶜ)
    (i : Fin ℓ) (k : ℕ) (hik : i.val < k) (hk : k ≤ ℓ)
    (hTinvariant : MapsTo T (Λ (D.index i)) (Λ (D.index i))) (x : X)
    (happroach : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index i),
      dist ((T : X → X)^[n + 1] x) y < r) :
    ∃ N : ℕ, 0 < N ∧ x ∈ interior (levels T A Λ ℓ N D k) ∧
      ∀ n : ℕ, (T : X → X)^[n] x ∈ levels T A Λ ℓ N D k ∩ interior Aᶜ := by
  obtain ⟨N, hN, hx⟩ := StableShiftEntry.exists_shift_containing_stable_start
    T A hA Λ ℓ D hsep i x happroach
  have hxk : x ∈ interior (levels T A Λ ℓ N D k) :=
    interior_mono (levels_monotone T A Λ ℓ N D (by omega)) hx
  have happ : AbsorbingBasinSeparation.Approaches T (Λ (D.index i)) x :=
    approaches_of_metric T (Λ (D.index i))
      (StableShiftEntry.basic_set_compact T A hA Λ ℓ N D i) x (by
        intro r hr
        obtain ⟨n, y, hy, hd⟩ := happroach r hr
        exact ⟨n + 1, y, hy, hd⟩)
  exact ⟨N, hN, hxk, stable_orbit_in_selected_live_prefix T A
    (levels T A Λ ℓ N D k) (Λ (D.index i)) hstrict
    (levels_positive_adapted T A Λ ℓ N D k (by omega) hk)
    (hsep _) hTinvariant x (interior_subset hxk) happ⟩

end ConditionedStochasticStabilityHyperbolic.Global.ActualStablePrefixEntry
