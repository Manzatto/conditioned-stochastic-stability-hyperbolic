module

public import ConditionedStochasticStabilityHyperbolic.Global.StableShiftEntry

/-! # The literal basic family inside a selected filtration prefix

All compactness, invariance and prefix-interior facts used by actual stochastic
basin controls follow from the source filtration's literal core identities.
-/
@[expose] public section
open Set Function Metric
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualPrefixBasicGeometry
open LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry
variable {X I : Type*} [MetricSpace X]

def basicFamily (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : ℕ) (hk : k ≤ ℓ) (i : Fin k) : Set X :=
  Λ (D.index ⟨i.val, i.isLt.trans_le hk⟩)

theorem actual_prefix_basic_properties
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (hsep : ∀ j, Λ j ⊆ interior Aᶜ)
    (k : ℕ) (hk : k ≤ ℓ) (i : Fin k) :
    IsCompact (basicFamily T A Λ ℓ D k hk i) ∧
    MapsTo T (basicFamily T A Λ ℓ D k hk i) (basicFamily T A Λ ℓ D k hk i) ∧
    MapsTo T.symm (basicFamily T A Λ ℓ D k hk i) (basicFamily T A Λ ℓ D k hk i) ∧
    basicFamily T A Λ ℓ D k hk i ⊆ interior (levels T A Λ ℓ N D k) ∩ interior Aᶜ := by
  let j : Fin ℓ := ⟨i.val, i.isLt.trans_le hk⟩
  change IsCompact (Λ (D.index j)) ∧ _
  have hfwd : MapsTo T (Λ (D.index j)) (Λ (D.index j)) := by
    rw [← literal_core T A Λ ℓ N D j]
    exact mapsTo_isolatedCore T _
  have hbwd : MapsTo T.symm (Λ (D.index j)) (Λ (D.index j)) := by
    rw [← literal_core T A Λ ℓ N D j]
    exact mapsTo_isolatedCore_symm T _
  refine ⟨StableShiftEntry.basic_set_compact T A hA Λ ℓ N D j, hfwd, hbwd, ?_⟩
  intro x hx
  refine ⟨?_, hsep _ hx⟩
  have hi := basic_set_interior_stratum T A Λ ℓ N D hsep j hx
  apply interior_mono (show filtrationLayer (levels T A Λ ℓ N D) j.val ⊆
      levels T A Λ ℓ N D k from fun y hy =>
    levels_monotone T A Λ ℓ N D (by dsimp [j]; omega) hy.1) hi

end ConditionedStochasticStabilityHyperbolic.Global.ActualPrefixBasicGeometry
