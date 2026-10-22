module
public import LeanShared.Geometry.FractionalManifoldRegularity
public import LeanShared.Analysis.CompactSupportedLocalHolder
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! For order strictly between zero and one, the actual fractional chart
condition on a Euclidean space yields local ordinary Hölder bounds. Compact
support upgrades these to a global constant in its ordinary norm metric. -/
public noncomputable section
open Set
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.FractionalManifoldRegularity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem local_holder_of_regular {f : E → F} {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hf : Regular (E := E) (F := F) a f) (x : E) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ W, ∀ z ∈ W, ‖f y - f z‖ ≤ C * ‖y - z‖ ^ a := by
  have floor : ⌊a⌋₊ = 0 := Nat.floor_eq_zero.mpr ha1
  have ne : a ≠ (⌊a⌋₊ : ℝ) := by simpa only [floor, Nat.cast_zero] using ha.ne'
  obtain ⟨W, hW, hx, _, C, hC, bound⟩ := hf.holder ne x
  have chart : chartMap (E := E) (F := F) f x = f := by
    simp [chartMap, chartAt_self_eq]
  refine ⟨W, hW, ?_, C, hC, fun y hy z hz => ?_⟩
  · simpa only [ext_chart_model_space_apply] using hx
  · have h := bound y hy z hz
    rw [floor, chart] at h
    simpa only [Nat.cast_zero, sub_zero, iteratedFDeriv_zero_eq_comp,
      Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map] using h

/-- This is a produced constant for the actual compactly supported rough
function, not a global-Hölder input to the approximation theorem. -/
theorem global_holder_of_regular [FiniteDimensional ℝ E]
    (f : E →ᵇ ℂ) (compact : HasCompactSupport f) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hf : Regular (E := E) (F := ℂ) a (fun x => f x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a := by
  simpa only [dist_eq_norm] using CompactSupportedLocalHolder.exists_bound f compact ha ha1.le
    (fun x => by simpa only [dist_eq_norm] using local_holder_of_regular ha ha1 hf x)
end LeanShared.FractionalManifoldRegularity
