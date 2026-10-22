module

public import ConditionedStochasticStabilityHyperbolic.Neighborhoods.Basic

/-! # The actual positive-weight collar and nonreturn neighborhood

Only positivity on the compact basic set is needed. The control region is
literally V intersected with the positive set of the actual weight; the
checked orbit neighborhood has closure in that region and keeps the
nonreturn property relative to the original isolating region.
-/

@[expose] public noncomputable section
open Set Metric
namespace ConditionedStochasticStabilityHyperbolic
variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_positive_weight_orbit_collar
    (T : X ≃ₜ X) (V Λ : Set X) (hV : IsOpen V) (hΛc : IsCompact Λ)
    (hΛ : Λ.Nonempty) (hΛV : Λ ⊆ V)
    (hcore : LeanShared.isolatedCore T (closure V) = Λ)
    (w : X → ℝ) (hw : Continuous w) (hwΛ : ∀ x ∈ Λ, 0 < w x) :
    ∃ (G U : Set X), G = V ∩ {x | 0 < w x} ∧ IsOpen G ∧ Λ ⊆ G ∧
      IsOpen U ∧ Λ ⊆ U ∧ closure U ⊆ G ∧
      (T '' closure U) ∩ LeanShared.forwardTrapped T (closure V) ⊆ U := by
  let G := V ∩ {x | 0 < w x}
  have hG : IsOpen G := hV.inter (isOpen_lt continuous_const hw)
  have hΛG : Λ ⊆ G := fun x hx => ⟨hΛV hx, hwΛ x hx⟩
  obtain ⟨ρ, hρ, hρG⟩ := hΛc.exists_cthickening_subset_open hG hΛG
  have hballG : closure (thickening ρ Λ) ⊆ G :=
    (closure_thickening_subset_cthickening ρ Λ).trans hρG
  obtain ⟨N, hN, hU, hΛU, _, hsep⟩ :=
    exists_orbitNeighborhood T hΛ hcore hρ (hballG.trans inter_subset_left)
  exact ⟨G, orbitNeighborhood T Λ ρ N, rfl, hG, hΛG, hU, hΛU,
    (closure_mono (orbitNeighborhood_subset_thickening (T := (T : X → X)) hΛ ρ hN)).trans
      hballG, hsep⟩

end ConditionedStochasticStabilityHyperbolic
