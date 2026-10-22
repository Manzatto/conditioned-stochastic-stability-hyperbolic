module

public import ConditionedStochasticStabilityHyperbolic.Neighborhoods.PositiveWeightCollar
public import LeanShared.Topology.PositiveWeightRobustness

/-! # One fixed positive collar for the forward and inverse noise arguments

The collar is constructed before noisy eigenvectors exist. Both w and
w∘T⁻¹ are positive on its closure. Uniform C0 inverse closeness supplies
positive inverse weights there for all sampled maps; no weight positivity
on the whole original live region is required.
-/

@[expose] public noncomputable section
open Set Metric
namespace ConditionedStochasticStabilityHyperbolic
variable {X Ω : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_twoSided_positive_orbit_collar
    (T : X ≃ₜ X) (V Λ : Set X) (hV : IsOpen V) (hΛc : IsCompact Λ)
    (hΛ : Λ.Nonempty) (hΛV : Λ ⊆ V)
    (hcore : LeanShared.isolatedCore T (closure V) = Λ)
    (w : X → ℝ) (hw : Continuous w) (hwΛ : ∀ x ∈ Λ, 0 < w x) :
    ∃ (G U : Set X), IsOpen G ∧ Λ ⊆ G ∧ closure G ⊆ V ∧
      (∀ x ∈ closure G, 0 < w x ∧ 0 < w (T.symm x)) ∧
      IsOpen U ∧ Λ ⊆ U ∧ closure U ⊆ G ∧
      (T '' closure U) ∩ LeanShared.forwardTrapped T (closure V) ⊆ U ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ H : X × Ω → X,
        (∀ x ∈ closure G, ∀ ω, dist (H (x, ω)) (T.symm x) < δ) →
        ∀ x ∈ closure G, ∀ ω, 0 < w (H (x, ω)) := by
  let W := V ∩ {x | 0 < w x} ∩ {x | 0 < w (T.symm x)}
  have hW : IsOpen W := (hV.inter (isOpen_lt continuous_const hw)).inter
    (isOpen_lt continuous_const (hw.comp T.symm.continuous))
  have hΛW : Λ ⊆ W := by
    intro x hx
    have hxi : T.symm x ∈ Λ := by
      rw [← hcore] at hx ⊢
      exact LeanShared.mapsTo_isolatedCore_symm T (closure V) hx
    exact ⟨⟨hΛV hx, hwΛ x hx⟩, hwΛ (T.symm x) hxi⟩
  obtain ⟨ρ, hρ, hρW⟩ := hΛc.exists_cthickening_subset_open hW hΛW
  let G := thickening ρ Λ
  have hG : IsOpen G := isOpen_thickening
  have hΛG : Λ ⊆ G := self_subset_thickening hρ Λ
  have hGW : closure G ⊆ W := (closure_thickening_subset_cthickening ρ Λ).trans hρW
  have hGV : closure G ⊆ V := fun _ hx => (hGW hx).1.1
  have hpositive : ∀ x ∈ closure G, 0 < w x ∧ 0 < w (T.symm x) :=
    fun _ hx => ⟨(hGW hx).1.2, (hGW hx).2⟩
  obtain ⟨ρ₂, hρ₂, hρ₂G⟩ := hΛc.exists_cthickening_subset_open hG hΛG
  have hballG : closure (thickening ρ₂ Λ) ⊆ G :=
    (closure_thickening_subset_cthickening ρ₂ Λ).trans hρ₂G
  obtain ⟨N, hN, hU, hΛU, _, hsep⟩ := exists_orbitNeighborhood T hΛ hcore hρ₂
    (hballG.trans (subset_closure.trans hGV))
  have hUG : closure (orbitNeighborhood T Λ ρ₂ N) ⊆ G :=
    (closure_mono (orbitNeighborhood_subset_thickening (T := (T : X → X)) hΛ ρ₂ hN)).trans hballG
  obtain ⟨δ, hδ, hnoise⟩ :=
    LeanShared.PositiveWeightRobustness.exists_noise_positive_composition_threshold (Ω := Ω)
      (closure G) isClosed_closure.isCompact T.symm T.symm.continuous.continuousOn w hw
      (fun x hx => (hpositive x hx).2)
  exact ⟨G, orbitNeighborhood T Λ ρ₂ N, hG, hΛG, hGV, hpositive,
    hU, hΛU, hUG, hsep, δ, hδ, hnoise⟩

end ConditionedStochasticStabilityHyperbolic
