module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring

/-! Exact coordinates and norm comparisons for finite frames orthonormal
for a separately named positive form. All estimates retain the original
norm on the ambient vector space. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.OrthogonalBilinearFrame
variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : V →L[ℝ] V →L[ℝ] ℝ) (e : ι → V)
    (orthogonal : ∀ i j, g (e i) (e j) = if i = j then 1 else 0)
include g orthogonal

theorem coordinate (c : ι → ℝ) (j : ι) :
    g (∑ i, c i • e i) (e j) = c j := by
  classical
  simp [map_sum, map_smul, orthogonal]

theorem quadratic (c : ι → ℝ) :
    g (∑ i, c i • e i) (∑ i, c i • e i) = ∑ i, (c i) ^ 2 := by
  classical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, coordinate g e orthogonal]
  simp only [smul_eq_mul, pow_two]

/-- The exact coordinate map is injective even when the index type is empty. -/
theorem combination_injective : Function.Injective (fun c : ι → ℝ => ∑ i, c i • e i) := by
  intro c d same
  change (∑ i, c i • e i) = ∑ i, d i • e i at same
  funext j
  rw [← coordinate g e orthogonal c j, ← coordinate g e orthogonal d j, same]

theorem lower_bound (A : ℝ) (bound : ∀ v : V, ‖v‖ ^ 2 ≤ A * g v v)
    (c : ι → ℝ) :
    ‖∑ i, c i • e i‖ ^ 2 ≤ A * ∑ i, (c i) ^ 2 := by
  simpa only [quadratic g e orthogonal] using bound (∑ i, c i • e i)

theorem upper_bound (B : ℝ) (bound : ∀ v : V, g v v ≤ B * ‖v‖ ^ 2)
    (c : ι → ℝ) :
    (∑ i, (c i) ^ 2) ≤ B * ‖∑ i, c i • e i‖ ^ 2 := by
  simpa only [quadratic g e orthogonal] using bound (∑ i, c i • e i)

end LeanShared.OrthogonalBilinearFrame
