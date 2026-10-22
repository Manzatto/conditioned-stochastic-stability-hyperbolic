module

public import ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSetup

/-! The geometry uses only a continuous extension of the live weight.
Fractional regularity is needed for products supported strictly inside the
analysis neighborhood, so no regular extension across the original closed
boundary is assumed. -/

public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSetup
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}
  (h : HL (E := E) T g Λ V) (w : M → ℝ) (W : Set M)


/-- Local cutoff-product calculus suffices; the ambient weight itself is
only continuous. This permits a Tietze extension of the original live weight. -/
def of_supported_product (hW : IsOpen W) (hΛW : Λ ⊆ W) (hWV : W ⊆ V)
    (hw : Continuous w)
    (agree : EqOn w g Λ)
    (smoothProduct : ∀ ζ : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ →
      tsupport ζ ⊆ W → FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) (ζ * w)) : Data h w W :=
  Classical.choice (by
    have positive : ∀ x ∈ Λ, 0 < w x := by
      intro x hx
      rw [agree hx]
      exact h.weight_positive x hx
    obtain ⟨G, B, hG, coreG, GW, pos, hB, coreB, BG, noReturn⟩ :=
      exists_twoSided_positive_orbit_collar_inside T V W Λ h.basic.open_neighborhood
        hW h.compact_core h.nonempty_core hΛW hWV h.actual_isolated_core.symm
        w hw positive
    obtain ⟨ζ, smooth, _, support, _, nonnegative, supportWeight, retained⟩ :=
      SmoothWeightCutoff.exists_weight_cutoff_of_local_nonnegative (E := E)
        (closure B) G isClosed_closure.isCompact hG BG w hw
        (fun x hx => (pos x (subset_closure hx)).1.le)
    have supported : tsupport (ζ * w) ⊆ W :=
      supportWeight.trans (subset_closure.trans GW)
    have coreAgree : EqOn (ζ * w) g Λ := fun x hx =>
      (retained (subset_closure (coreB hx))).trans (agree hx)
    let fresh : HL (E := E) T (ζ * w) Λ W := {
      r := h.r
      regularity_gt_one := h.regularity_gt_one
      map_regular := h.map_regular
      inverse_regular := h.inverse_regular
      basic := {
        hyperbolic := h.basic.hyperbolic
        nonempty := h.nonempty_core
        open_neighborhood := hW
        subset_neighborhood := hΛW
        isolated := analysis_core h W hΛW hWV
        dense_orbit := h.basic.dense_orbit }
      weight_regular := smoothProduct ζ smooth (support.trans (subset_closure.trans GW))
      weight_nonnegative := nonnegative
      weight_supported := supported
      weight_positive := fun x hx => (coreAgree hx).symm ▸ h.weight_positive x hx
      mixing := h.mixing }
    exact ⟨{
      collar := G
      retained := B
      cutoff := ζ
      collar_open := hG
      core_collar := coreG
      collar_live := GW
      positive := pos
      retained_open := hB
      core_retained := coreB
      retained_collar := BG
      no_return := noReturn
      cutoff_smooth := smooth
      cutoff_support := support
      weight_nonnegative := nonnegative
      weight_support := supported
      weight_agreement := retained
      core_agreement := coreAgree
      fresh := fresh
      regularity_eq := rfl
      hyperbolic_eq := rfl }⟩)

end ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSetup
