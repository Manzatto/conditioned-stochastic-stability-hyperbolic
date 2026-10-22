module
public import LeanShared.Geometry.FractionalManifoldRegularity
public import LeanShared.Geometry.BoundedHolderSpace
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Actual Hölder bounds imply the literal fractional chart condition for
orders between zero and one. This supplies regularity of every vector in
the concrete lower Hölder spaces; it is not a regularity source field. -/
public noncomputable section
open Set
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.FractionalManifoldRegularity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem regular_of_holder {f : E → F} {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (continuous : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (bound : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) :
    Regular (E := E) (F := F) a f := by
  have floor : ⌊a⌋₊ = 0 := Nat.floor_eq_zero.mpr ha1
  refine ⟨ha.le, ?_, ?_⟩
  · rw [floor]
    exact (contDiff_zero.mpr continuous).contMDiff
  · intro _ x
    have chart : chartMap (E := E) (F := F) f x = f := by
      simp [chartMap, chartAt_self_eq]
    have domain : chartDomain (E := E) (F := F) f x = univ := by
      simp [chartDomain, chartAt_self_eq]
    refine ⟨univ, isOpen_univ, mem_univ _, ?_, C, hC, fun y _ z _ => ?_⟩
    · rw [domain]
    · rw [floor, chart]
      simpa only [Nat.cast_zero, sub_zero, iteratedFDeriv_zero_eq_comp,
        Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map] using bound y z

theorem graph_regular {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (v : BoundedHolderSpace.graph E a) :
    Regular (E := E) (F := ℂ) a (fun x => BoundedHolderSpace.physical E a v x) :=
  regular_of_holder ha ha1 (BoundedHolderSpace.physical E a v).continuous (norm_nonneg v)
    (fun x y => by simpa only [dist_eq_norm] using BoundedHolderSpace.increment_bound E a v x y)
end LeanShared.FractionalManifoldRegularity
