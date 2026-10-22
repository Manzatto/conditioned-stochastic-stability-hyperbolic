module
public import LeanShared.Geometry.CompactSmoothHolderGraph
public import LeanShared.Geometry.BoundedHolderOfBoundNorm

/-! Translated smooth tests form a Lipschitz family of Hölder graph elements. For smooth
compactly supported `w` and `ρ`, the tests `z ↦ w z * ρ (z - y)` are Hölder graph elements
depending Lipschitz-continuously on the translation parameter `y`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set
open scoped ContDiff BoundedContinuousFunction NNReal
namespace LeanShared.TranslatedHolderTests

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A graph element is controlled by a sup bound and a Lipschitz bound of its physical
function. -/
theorem graph_norm_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (v : BoundedHolderSpace.graph E b)
    (Z Λ : ℝ) (hZ : 0 ≤ Z) (hΛ : 0 ≤ Λ)
    (sup : ∀ z, ‖BoundedHolderSpace.physical E b v z‖ ≤ Z)
    (lip : ∀ z z', ‖BoundedHolderSpace.physical E b v z - BoundedHolderSpace.physical E b v z'‖ ≤
      Λ * dist z z') :
    ‖v‖ ≤ 2 * Z + Λ := by
  let f := BoundedHolderSpace.physical E b v
  have holder : ∀ x y, ‖f x - f y‖ ≤ (2 * Z + Λ) * dist x y ^ b := by
    intro x y
    have hpow : 0 ≤ dist x y ^ b := Real.rpow_nonneg dist_nonneg _
    by_cases h : dist x y ≤ 1
    · calc ‖f x - f y‖ ≤ Λ * dist x y := lip x y
        _ ≤ Λ * dist x y ^ b :=
          mul_le_mul_of_nonneg_left (NativeChartTest.small_le_rpow dist_nonneg h hb hb1) hΛ
        _ ≤ (2 * Z + Λ) * dist x y ^ b :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hpow
    · have hone : 1 ≤ dist x y ^ b := Real.one_le_rpow (le_of_lt (not_le.mp h)) hb.le
      calc ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
        _ ≤ 2 * Z := by linarith [sup x, sup y]
        _ ≤ (2 * Z + Λ) * 1 := by rw [mul_one]; linarith
        _ ≤ (2 * Z + Λ) * dist x y ^ b := mul_le_mul_of_nonneg_left hone (by positivity)
  have same : v = BoundedHolderSpace.ofBound E b f (2 * Z + Λ) holder :=
    BoundedHolderSpace.physical_injective E b rfl
  rw [same]
  refine (BoundedHolderSpace.norm_ofBound_le E b f (by positivity) holder).trans ?_
  refine max_le ?_ le_rfl
  have fle : ‖f‖ ≤ Z := (BoundedContinuousFunction.norm_le hZ).mpr sup
  linarith

/-- Translated smooth tests are a Lipschitz family of Hölder graph elements. -/
theorem translated_family {w ρ : E → ℂ} (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ v : E → BoundedHolderSpace.graph E b,
      (∀ y z, BoundedHolderSpace.physical E b (v y) z = w z * ρ (z - y)) ∧
      ∃ K : ℝ, ∀ y y', ‖v y - v y'‖ ≤ K * dist y y' := by
  have smooth (y : E) : ContDiff ℝ ∞ (fun z => w z * ρ (z - y)) :=
    hw.mul (hρ.comp (contDiff_id.sub contDiff_const))
  have compact (y : E) : HasCompactSupport (fun z => w z * ρ (z - y)) := hwc.mul_right
  choose v hv using fun y => CompactSmoothHolderGraph.exists_graph (smooth y) (compact y) hb hb1
  refine ⟨v, hv, ?_⟩
  obtain ⟨Lw, lipW⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hwc hw (by simp)
  obtain ⟨Lρ, lipρ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hρc hρ (by simp)
  obtain ⟨LD, lipD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hρc.fderiv (𝕜 := ℝ))
    (hρ.fderiv_right (m := 1) (by simp)) (by simp)
  obtain ⟨Zw, hZw⟩ := hw.continuous.norm.bddAbove_range_of_hasCompactSupport hwc.norm
  have hZwx : ∀ z, ‖w z‖ ≤ Zw := fun z => hZw ⟨z, rfl⟩
  have Zw0 : 0 ≤ Zw := (norm_nonneg _).trans (hZwx 0)
  refine ⟨2 * (Zw * Lρ) + ((Lw : ℝ) * Lρ + Zw * LD), fun y y' => ?_⟩
  set δ := dist y y' with hδ
  have δ0 : 0 ≤ δ := dist_nonneg
  let u : E → ℂ := fun x => ρ (x - y) - ρ (x - y')
  have uBound (x : E) : ‖u x‖ ≤ Lρ * δ := by
    have := lipρ.dist_le_mul (x - y) (x - y')
    rw [dist_eq_norm, dist_eq_norm] at this
    rw [hδ, dist_comm, dist_eq_norm]
    calc ‖u x‖ = ‖ρ (x - y) - ρ (x - y')‖ := rfl
      _ ≤ Lρ * ‖x - y - (x - y')‖ := this
      _ = Lρ * ‖y' - y‖ := by congr 2; abel
  have uLip (z z' : E) : ‖u z - u z'‖ ≤ (LD * δ) * dist z z' := by
    have hasDeriv (x : E) : HasFDerivAt u (fderiv ℝ ρ (x - y) - fderiv ℝ ρ (x - y')) x := by
      have shifted (c : E) : HasFDerivAt (fun x => ρ (x - c)) (fderiv ℝ ρ (x - c)) x := by
        have h := ((hρ.differentiable (by simp)) (x - c)).hasFDerivAt.comp x
          ((hasFDerivAt_id x).sub_const c)
        rw [ContinuousLinearMap.comp_id] at h
        exact h
      exact (shifted y).sub (shifted y')
    have diff (x : E) : DifferentiableAt ℝ u x := (hasDeriv x).differentiableAt
    have deriv (x : E) : ‖fderiv ℝ u x‖ ≤ LD * δ := by
      rw [(hasDeriv x).fderiv, ← dist_eq_norm]
      calc dist (fderiv ℝ ρ (x - y)) (fderiv ℝ ρ (x - y')) ≤ LD * dist (x - y) (x - y') :=
            lipD.dist_le_mul _ _
        _ = LD * δ := by
            rw [hδ, dist_eq_norm, dist_eq_norm, show x - y - (x - y') = y' - y by abel,
              ← norm_neg, neg_sub]
    have mv := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (fun x _ => diff x)
      (fun x _ => deriv x) convex_univ (mem_univ z') (mem_univ z)
    rw [dist_eq_norm]
    exact mv
  refine (TranslatedHolderTests.graph_norm_le hb hb1 (v y - v y') (Zw * Lρ * δ)
    (((Lw : ℝ) * Lρ + Zw * LD) * δ) (by positivity) (by positivity) ?_ ?_).trans
      (le_of_eq (by ring))
  · intro z
    rw [map_sub, BoundedContinuousFunction.sub_apply, hv, hv]
    calc ‖w z * ρ (z - y) - w z * ρ (z - y')‖ = ‖w z‖ * ‖u z‖ := by rw [← mul_sub, norm_mul]
      _ ≤ Zw * (Lρ * δ) := mul_le_mul (hZwx z) (uBound z) (norm_nonneg _) Zw0
      _ = Zw * Lρ * δ := by ring
  · intro z z'
    rw [map_sub, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.sub_apply,
      hv, hv, hv, hv]
    have split : w z * ρ (z - y) - w z * ρ (z - y') - (w z' * ρ (z' - y) - w z' * ρ (z' - y')) =
        (w z - w z') * u z + w z' * (u z - u z') := by
      simp only [u]; ring
    rw [split]
    have wl : ‖w z - w z'‖ ≤ Lw * dist z z' := by
      rw [← dist_eq_norm]; exact lipW.dist_le_mul z z'
    calc ‖(w z - w z') * u z + w z' * (u z - u z')‖
        ≤ ‖w z - w z'‖ * ‖u z‖ + ‖w z'‖ * ‖u z - u z'‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ (Lw * dist z z') * (Lρ * δ) + Zw * ((LD * δ) * dist z z') :=
          add_le_add (mul_le_mul wl (uBound z) (norm_nonneg _) (by positivity))
            (mul_le_mul (hZwx z') (uLip z z') (norm_nonneg _) Zw0)
      _ = ((Lw : ℝ) * Lρ + Zw * LD) * δ * dist z z' := by ring

end LeanShared.TranslatedHolderTests
