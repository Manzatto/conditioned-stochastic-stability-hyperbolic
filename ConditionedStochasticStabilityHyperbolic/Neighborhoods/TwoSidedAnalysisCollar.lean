module

public import ConditionedStochasticStabilityHyperbolic.Neighborhoods.TwoSidedPositiveCollar

/-! A small analysis collar with nonreturn measured in the original live
region. Shrinking the collar does not change the process being studied. -/

@[expose] public noncomputable section
open Set Metric
namespace ConditionedStochasticStabilityHyperbolic
variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_twoSided_positive_orbit_collar_inside
    (T : X ≃ₜ X) (V W Λ : Set X) (_hV : IsOpen V) (hW : IsOpen W)
    (hΛc : IsCompact Λ) (hΛ : Λ.Nonempty) (hΛW : Λ ⊆ W) (hWV : W ⊆ V)
    (hcore : LeanShared.isolatedCore T (closure V) = Λ)
    (w : X → ℝ) (hw : Continuous w) (hwΛ : ∀ x ∈ Λ, 0 < w x) :
    ∃ (G B : Set X), IsOpen G ∧ Λ ⊆ G ∧ closure G ⊆ W ∧
      (∀ x ∈ closure G, 0 < w x ∧ 0 < w (T.symm x)) ∧
      IsOpen B ∧ Λ ⊆ B ∧ closure B ⊆ G ∧
      (T '' closure B) ∩ LeanShared.forwardTrapped T (closure V) ⊆ B := by
  let P := W ∩ {x | 0 < w x} ∩ {x | 0 < w (T.symm x)}
  have hP : IsOpen P := (hW.inter (isOpen_lt continuous_const hw)).inter
    (isOpen_lt continuous_const (hw.comp T.symm.continuous))
  have hΛP : Λ ⊆ P := by
    intro x hx
    have hxi : T.symm x ∈ Λ := by
      rw [← hcore] at hx ⊢
      exact LeanShared.mapsTo_isolatedCore_symm T (closure V) hx
    exact ⟨⟨hΛW hx, hwΛ x hx⟩, hwΛ (T.symm x) hxi⟩
  obtain ⟨ρ, hρ, hρP⟩ := hΛc.exists_cthickening_subset_open hP hΛP
  let G := thickening ρ Λ
  have hG : IsOpen G := isOpen_thickening
  have hΛG : Λ ⊆ G := self_subset_thickening hρ Λ
  have hGP : closure G ⊆ P := (closure_thickening_subset_cthickening ρ Λ).trans hρP
  have hGW : closure G ⊆ W := fun _ hx => (hGP hx).1.1
  have hpositive : ∀ x ∈ closure G, 0 < w x ∧ 0 < w (T.symm x) :=
    fun _ hx => ⟨(hGP hx).1.2, (hGP hx).2⟩
  obtain ⟨ρ₂, hρ₂, hρ₂G⟩ := hΛc.exists_cthickening_subset_open hG hΛG
  have hballG : closure (thickening ρ₂ Λ) ⊆ G :=
    (closure_thickening_subset_cthickening ρ₂ Λ).trans hρ₂G
  obtain ⟨N, hN, hB, hΛB, _, hsep⟩ := exists_orbitNeighborhood T hΛ hcore hρ₂
    (hballG.trans (subset_closure.trans (hGW.trans hWV)))
  have hBG : closure (orbitNeighborhood T Λ ρ₂ N) ⊆ G :=
    (closure_mono (orbitNeighborhood_subset_thickening (T := (T : X → X)) hΛ ρ₂ hN)).trans hballG
  exact ⟨G, orbitNeighborhood T Λ ρ₂ N, hG, hΛG, hGW, hpositive, hB, hΛB, hBG, hsep⟩

end ConditionedStochasticStabilityHyperbolic
