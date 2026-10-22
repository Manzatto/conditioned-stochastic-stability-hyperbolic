module
public import LeanShared.Geometry.EuclideanRoughHolderRealization
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Every actual supported C^u function, for ANY u above a fixed
lower Hölder order b∈(0,1), is represented in the constructed little
space. Orders u≥1 use their actual first derivative; they are not
misinterpreted as value-only Hölder orders greater than one. -/
public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction ContDiff
namespace LeanShared.EuclideanSmoothHolderCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {V : Set E} (hV : IsCompact (closure V)) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)

include μ in
theorem exists_lower_of_any_regular (f : E →ᵇ ℂ) (openV : IsOpen V)
    (support : tsupport f ⊆ V) (compact : HasCompactSupport f)
    {u : ℝ} (hbu : b < u)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℂ) u (fun x => f x)) :
    ∃ v : space hV hb hb1, physical hV hb hb1 v = f := by
  by_cases hu : u < 1
  · exact exists_lower_of_regular μ hV hb hb1 f openV support compact
      (hb.trans hbu) hu hbu regular
  · have floor : 1 ≤ ⌊u⌋₊ := (Nat.one_le_floor_iff u).mpr (le_of_not_gt hu)
    have c1 : ContDiff ℝ 1 (fun x => f x) := regular.differentiable.contDiff.of_le (by
      exact_mod_cast floor)
    obtain ⟨C, bound⟩ := ContDiff.lipschitzWith_of_hasCompactSupport compact c1 (by decide)
    have estimate : ∀ x y, ‖f x - f y‖ ≤ (C : ℝ) * ‖x - y‖ ^ (1 : ℝ) := by
      intro x y
      simpa only [Real.rpow_one, dist_eq_norm] using bound.dist_le_mul x y
    exact ⟨⟨BumpLowerHolderConvergence.lift f hb.le hb1 C.coe_nonneg estimate,
      lower_mem μ hV hb hb1 f openV support compact hb1 C.coe_nonneg estimate⟩, rfl⟩
end LeanShared.EuclideanSmoothHolderCore
