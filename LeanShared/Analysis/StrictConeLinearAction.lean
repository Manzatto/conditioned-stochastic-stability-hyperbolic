module
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.FunProp

/-! Strict action on a closed cone gives an actual operator-norm neighborhood
preserving the entire cone. The radius is derived using the compact unit
slice, not supplied as a random-map cone certificate. -/
public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.StrictConeLinearAction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_radius {C : Set E} {D : Set F} (closed : IsClosed C)
    (sourceScale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (targetZero : (0 : F) ∈ D)
    (targetScale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ D, r • v ∈ D)
    (A : E →L[ℝ] F)
    (strict : ∀ v ∈ C ∩ Metric.sphere (0 : E) 1, A v ∈ interior D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ B : E →L[ℝ] F, ‖B - A‖ ≤ δ → ∀ v ∈ C, B v ∈ D := by
  have compact : IsCompact (C ∩ Metric.sphere (0 : E) 1) :=
    (isCompact_sphere (0 : E) 1).inter_left closed
  have evaluation : Continuous (fun p : (E →L[ℝ] F) × E => p.1 p.2) := by fun_prop
  have eventual : ∀ᶠ B in 𝓝 A, ∀ v ∈ C ∩ Metric.sphere (0 : E) 1, B v ∈ D := by
    apply compact.eventually_forall_of_forall_eventually
    intro v hv
    have h : (fun p : (E →L[ℝ] F) × E => p.1 p.2) ⁻¹' interior D ∈ 𝓝 (A, v) :=
      (evaluation.continuousAt (x := (A, v))).preimage_mem_nhds
        (isOpen_interior.mem_nhds (strict v hv))
    filter_upwards [h] with p hp
    exact interior_subset hp
  obtain ⟨r, positive, ball⟩ := Metric.mem_nhds_iff.mp eventual
  refine ⟨r / 2, half_pos positive, fun B close v hv => ?_⟩
  have near : B ∈ Metric.ball A r := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact close.trans_lt (half_lt_self positive)
  by_cases zero : v = 0
  · simpa only [zero, map_zero] using targetZero
  have vn : 0 < ‖v‖ := norm_pos_iff.mpr zero
  have normalized : ‖v‖⁻¹ • v ∈ C ∩ Metric.sphere (0 : E) 1 := by
    refine ⟨sourceScale _ (inv_nonneg.mpr vn.le) _ hv, ?_⟩
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr vn.le), inv_mul_cancel₀ (ne_of_gt vn)]
  have member := targetScale ‖v‖ vn.le _ (ball near _ normalized)
  simpa only [map_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt vn), one_smul] using member
end LeanShared.StrictConeLinearAction
