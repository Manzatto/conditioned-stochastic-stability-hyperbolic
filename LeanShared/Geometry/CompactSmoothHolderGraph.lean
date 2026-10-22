module
public import LeanShared.Geometry.NativeChartTest
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! A smooth compactly supported function on a finite-dimensional space is a
Hölder graph element of every order `b ∈ (0,1]`: it is bounded and Lipschitz,
so its increments are at most `(2Z + Λ) · dist^b`. -/
public noncomputable section
open Set
open scoped ContDiff BoundedContinuousFunction
namespace LeanShared.CompactSmoothHolderGraph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_graph {ψ : E → ℂ} (smooth : ContDiff ℝ ∞ ψ) (compact : HasCompactSupport ψ)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ v : BoundedHolderSpace.graph E b, ∀ x, BoundedHolderSpace.physical E b v x = ψ x := by
  obtain ⟨Λ, lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport compact smooth (by simp)
  obtain ⟨Z, hZ⟩ := smooth.continuous.norm.bddAbove_range_of_hasCompactSupport compact.norm
  have hZx : ∀ x, ‖ψ x‖ ≤ Z := fun x => hZ ⟨x, rfl⟩
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZx 0)
  let f : E →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup ψ smooth.continuous Z hZx
  have holder : ∀ x y, ‖f x - f y‖ ≤ (2 * Z + Λ) * dist x y ^ b := by
    intro x y
    change ‖ψ x - ψ y‖ ≤ _
    have hpow : 0 ≤ dist x y ^ b := Real.rpow_nonneg dist_nonneg _
    by_cases h : dist x y ≤ 1
    · have hl : ‖ψ x - ψ y‖ ≤ Λ * dist x y := by
        rw [← dist_eq_norm]
        exact lip.dist_le_mul x y
      calc ‖ψ x - ψ y‖ ≤ Λ * dist x y := hl
        _ ≤ Λ * dist x y ^ b :=
          mul_le_mul_of_nonneg_left (NativeChartTest.small_le_rpow dist_nonneg h hb hb1)
            Λ.coe_nonneg
        _ ≤ (2 * Z + Λ) * dist x y ^ b :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hpow
    · have hone : 1 ≤ dist x y ^ b := Real.one_le_rpow (le_of_lt (not_le.mp h)) hb.le
      calc ‖ψ x - ψ y‖ ≤ ‖ψ x‖ + ‖ψ y‖ := norm_sub_le _ _
        _ ≤ 2 * Z := by linarith [hZx x, hZx y]
        _ ≤ (2 * Z + Λ) * 1 := by rw [mul_one]; exact le_add_of_nonneg_right Λ.coe_nonneg
        _ ≤ (2 * Z + Λ) * dist x y ^ b :=
          mul_le_mul_of_nonneg_left hone (by positivity)
  exact ⟨BoundedHolderSpace.ofBound E b f (2 * Z + Λ) holder, fun x => rfl⟩

end LeanShared.CompactSmoothHolderGraph
