module

public import ConditionedStochasticStabilityHyperbolic.Paper.Hypotheses
public import ConditionedStochasticStabilityHyperbolic.Neighborhoods.PositiveWeightCollar
public import LeanShared.Geometry.PositiveWeightCutoff

/-! A fresh HL cutoff comes from the actual process weight's regular
extension, not from a merely continuous Tietze extension. Its sign outside
the closed live region is irrelevant. Ordinary fractional smooth-product
closure is an explicit calculus input; all geometric, positivity and HL
replacement claims are proved here. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)

/-- The input w is the genuine regular extension. The ordinary calculus
source only asserts closure of its fractional regularity under smooth
multiplication; it contains no spectral or conditioned conclusion. -/
theorem exists_fresh_HL_weight (w : M → ℝ)
    (hw : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) w)
    (agree : EqOn w g Λ)
    (smoothProduct : ∀ ζ : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ →
      FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) (ζ * w)) :
    ∃ (G U : Set M) (ζ : M → ℝ),
      G = V ∩ {x | 0 < w x} ∧ IsOpen G ∧ IsOpen U ∧ Λ ⊆ U ∧ closure U ⊆ G ∧
      (T '' closure U) ∩ forwardTrapped T (closure V) ⊆ U ∧
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ ∧ tsupport ζ ⊆ G ∧
      EqOn (ζ * w) w (closure U) ∧ EqOn (ζ * w) g Λ ∧
      ∃ fresh : HL (E := E) T (ζ * w) Λ V,
        fresh.r = h.r ∧ fresh.basic = h.basic := by
  have hwc : Continuous w := hw.differentiable.continuous
  have hwpos : ∀ x ∈ Λ, 0 < w x := by
    intro x hx
    rw [agree hx]
    exact h.weight_positive x hx
  obtain ⟨G, U, hGdef, hG, _, hU, hΛU, hUG, hsep⟩ :=
    exists_positive_weight_orbit_collar T V Λ h.basic.open_neighborhood
      h.compact_core h.nonempty_core h.basic.subset_neighborhood h.actual_isolated_core.symm
      w hwc hwpos
  obtain ⟨ζ, smooth, _, support, _, nonnegative, supportWeight, retained⟩ :=
    SmoothWeightCutoff.exists_weight_cutoff_of_local_nonnegative (E := E)
      (closure U) G isClosed_closure.isCompact hG hUG w hwc (by
        intro x hx
        rw [hGdef] at hx
        exact hx.2.le)
  have coreAgree : EqOn (ζ * w) g Λ := fun x hx =>
    (retained (subset_closure (hΛU hx))).trans (agree hx)
  let fresh : HL (E := E) T (ζ * w) Λ V := {
    r := h.r
    regularity_gt_one := h.regularity_gt_one
    map_regular := h.map_regular
    inverse_regular := h.inverse_regular
    basic := h.basic
    weight_regular := smoothProduct ζ smooth
    weight_nonnegative := nonnegative
    weight_supported := supportWeight.trans (by rw [hGdef]; exact inter_subset_left)
    weight_positive := fun x hx => (coreAgree hx).symm ▸ h.weight_positive x hx
    mixing := h.mixing }
  exact ⟨G, U, ζ, hGdef, hG, hU, hΛU, hUG, hsep, smooth, support,
    retained, coreAgree, fresh, rfl, rfl⟩

end ConditionedStochasticStabilityHyperbolic.Paper.HL
