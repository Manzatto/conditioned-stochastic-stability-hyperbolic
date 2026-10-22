module

public import ConditionedStochasticStabilityHyperbolic.Paper.FreshRegularWeight
public import Mathlib.Topology.Separation.Regular

/-! An adapted BT domain need only contain the isolated core. The analysis
neighborhood is chosen inside that domain; the original closed live state
is retained separately by the local stochastic-stability consumer. -/

public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)

/-- Shrinking the analysis domain preserves the original isolated core.
Only ordinary multiplication of a fractional-regular weight by a smooth
cutoff is supplied. The actual cutoff and the new HL datum are constructed. -/
theorem exists_adapted_analysis_HL (O : Set M) (hO : IsOpen O) (hΛO : Λ ⊆ O)
    (w : M → ℝ)
    (hw : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) w)
    (agree : EqOn w g Λ)
    (smoothProduct : ∀ ζ : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ →
      FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) (ζ * w)) :
    ∃ (W : Set M) (ζ : M → ℝ), IsOpen W ∧ Λ ⊆ W ∧ closure W ⊆ O ∩ V ∧
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ ∧ tsupport ζ ⊆ W ∧
      EqOn (ζ * w) g Λ ∧
      ∃ fresh : HL (E := E) T (ζ * w) Λ W,
        fresh.r = h.r ∧ fresh.basic.hyperbolic = h.basic.hyperbolic := by
  obtain ⟨W, hW, hΛW, hWO⟩ := h.compact_core.exists_isOpen_closure_subset
    ((hO.inter h.basic.open_neighborhood).mem_nhdsSet.mpr (subset_inter hΛO h.basic.subset_neighborhood))
  have core : Λ = isolatedCore T (closure W) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxold : x ∈ isolatedCore T (closure V) := h.actual_isolated_core ▸ hx
      exact ⟨fun n => subset_closure (hΛW (h.actual_isolated_core.symm ▸
        iterate_mem_isolatedCore T (closure V) hxold n)),
        fun n => subset_closure (hΛW (h.actual_isolated_core.symm ▸
          iterate_symm_mem_isolatedCore T (closure V) hxold n))⟩
    · intro x hx
      apply h.actual_isolated_core.symm ▸ (show x ∈ isolatedCore T (closure V) from ?_)
      exact ⟨fun n => subset_closure (hWO (hx.1 n)).2,
        fun n => subset_closure (hWO (hx.2 n)).2⟩
  have hwc : Continuous w := hw.differentiable.continuous
  let P := W ∩ {x | 0 < w x}
  have hP : IsOpen P := hW.inter (isOpen_lt continuous_const hwc)
  have hΛP : Λ ⊆ P := by
    intro x hx
    refine ⟨hΛW hx, ?_⟩
    change 0 < w x
    rw [agree hx]
    exact h.weight_positive x hx
  obtain ⟨ζ, hsmooth, _, hsupp, _, hnonneg, hwsupp, heq⟩ :=
    SmoothWeightCutoff.exists_weight_cutoff_of_local_nonnegative (E := E)
      Λ P h.compact_core hP hΛP w hwc (fun _ hx => hx.2.le)
  have hagree : EqOn (ζ * w) g Λ := fun _ hx => (heq hx).trans (agree hx)
  refine ⟨W, ζ, hW, hΛW, hWO, hsmooth, hsupp.trans inter_subset_left, hagree, ?_⟩
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
      isolated := core
      dense_orbit := h.basic.dense_orbit }
    weight_regular := smoothProduct ζ hsmooth
    weight_nonnegative := hnonneg
    weight_supported := hwsupp.trans inter_subset_left
    weight_positive := fun x hx => (hagree hx).symm ▸ h.weight_positive x hx
    mixing := h.mixing }
  exact ⟨fresh, rfl, rfl⟩

end ConditionedStochasticStabilityHyperbolic.Paper.HL
