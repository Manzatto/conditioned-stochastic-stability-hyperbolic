module
public import LeanShared.Geometry.ChartLocalization
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The Euclidean pairing of the chart coordinate of a bounded continuous function with a
bounded continuous test is a bounded linear functional. The cutoff is continuous with
compact support inside the chart source. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ChartFunctionPairing
open ChartLocalization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] (e : OpenPartialHomeomorph M E) (θ : M → ℂ)
  (hsupp : tsupport θ ⊆ e.source) (hcompact : HasCompactSupport θ) (hθ : Continuous θ)

include hsupp hcompact hθ in
theorem coordinate_continuous (F : M → ℂ) (hF : Continuous F) : Continuous (coordinate e θ F) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ e.target
  · have hc : ContinuousAt (fun y => θ (e.symm y) * F (e.symm y)) x :=
      (hθ.continuousAt.comp (e.continuousAt_symm hx)).mul (hF.continuousAt.comp (e.continuousAt_symm hx))
    apply hc.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    exact ite_eq_left hy
  · have hxc : x ∉ localSupport e θ := fun hc => hx (localSupport_subset_target e θ hsupp hc)
    have hc : ContinuousAt (fun _ : E => (0 : ℂ)) x := continuousAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [(localSupport_isCompact e θ hsupp hcompact).isClosed.isOpen_compl.mem_nhds hxc]
      with y hy
    exact coordinate_zero_outside e θ F y hy

theorem coordinate_norm_le (F : M → ℂ) {Cθ CF : ℝ} (hCθ : 0 ≤ Cθ) (hCF : 0 ≤ CF)
    (boundθ : ∀ x, ‖θ x‖ ≤ Cθ) (boundF : ∀ x, ‖F x‖ ≤ CF) (y : E) :
    ‖coordinate e θ F y‖ ≤ Cθ * CF := by
  unfold coordinate
  split_ifs
  · rw [norm_mul]
    exact mul_le_mul (boundθ _) (boundF _) (norm_nonneg _) hCθ
  · rw [norm_zero]; positivity

theorem coordinate_add (F G : M → ℂ) : coordinate e θ (F + G) = coordinate e θ F + coordinate e θ G := by
  funext y
  simp only [coordinate, Pi.add_apply]
  split_ifs <;> ring

theorem coordinate_smul (c : ℂ) (F : M → ℂ) : coordinate e θ (c • F) = c • coordinate e θ F := by
  funext y
  simp only [coordinate, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ] (w : E →ᵇ ℂ)

include hsupp hcompact hθ in
theorem integrable (F : M →ᵇ ℂ) : Integrable (fun z => coordinate e θ F z * w z) μ := by
  have cont : Continuous (fun z => coordinate e θ F z * w z) :=
    (coordinate_continuous e θ hsupp hcompact hθ F F.continuous).mul w.continuous
  exact cont.integrable_of_hasCompactSupport
    ((coordinate_hasCompactSupport e θ hsupp hcompact F).mul_right)

/-- The chart pairing as a bounded linear functional. -/
@[expose] def pairing : (M →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫ z, coordinate e θ F z * w z ∂μ
      map_add' := fun F G => by
        rw [BoundedContinuousFunction.coe_add, coordinate_add]
        simp only [Pi.add_apply, add_mul]
        exact integral_add (integrable e θ hsupp hcompact hθ μ w F)
          (integrable e θ hsupp hcompact hθ μ w G)
      map_smul' := fun c F => by
        have h : (⇑(c • F) : M → ℂ) = c • (⇑F : M → ℂ) := by funext x; rfl
        rw [h, coordinate_smul]
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
    ((μ (localSupport e θ)).toReal *
      ((hθ.norm.bddAbove_range_of_hasCompactSupport hcompact.norm).choose ⊔ 0) * ‖w‖)
    (fun F => by
      set Cθ := (hθ.norm.bddAbove_range_of_hasCompactSupport hcompact.norm).choose ⊔ 0
      have boundθ : ∀ x, ‖θ x‖ ≤ Cθ := fun x =>
        ((hθ.norm.bddAbove_range_of_hasCompactSupport hcompact.norm).choose_spec ⟨x, rfl⟩).trans
          le_sup_left
      have hCθ : 0 ≤ Cθ := le_sup_right
      change ‖∫ z, coordinate e θ F z * w z ∂μ‖ ≤ _
      have pointwise (z : E) : ‖coordinate e θ F z * w z‖ ≤
          (localSupport e θ).indicator (fun _ => Cθ * ‖F‖ * ‖w‖) z := by
        by_cases hz : z ∈ localSupport e θ
        · rw [indicator_of_mem hz, norm_mul]
          exact mul_le_mul (coordinate_norm_le e θ F hCθ (norm_nonneg _) boundθ
            (fun x => F.norm_coe_le_norm x) z) (w.norm_coe_le_norm z) (norm_nonneg _)
            (by positivity)
        · rw [indicator_of_notMem hz, coordinate_zero_outside e θ F z hz, zero_mul, norm_zero]
      have measurableSupport : MeasurableSet (localSupport e θ) :=
        (localSupport_isCompact e θ hsupp hcompact).isClosed.measurableSet
      have finite : μ (localSupport e θ) ≠ ⊤ :=
        (localSupport_isCompact e θ hsupp hcompact).measure_lt_top.ne
      have intBound : Integrable ((localSupport e θ).indicator (fun _ => Cθ * ‖F‖ * ‖w‖)) μ :=
        (integrableOn_const finite).integrable_indicator measurableSupport
      refine (norm_integral_le_of_norm_le intBound (ae_of_all _ pointwise)).trans ?_
      rw [integral_indicator_const _ measurableSupport, smul_eq_mul, measureReal_def]
      apply le_of_eq
      ring)

theorem pairing_apply (F : M →ᵇ ℂ) :
    pairing e θ hsupp hcompact hθ μ w F = ∫ z, coordinate e θ F z * w z ∂μ := rfl

end LeanShared.ChartFunctionPairing
