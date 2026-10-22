module
public import LeanShared.Geometry.BoundedRiemannianInverseChartCompact
public import LeanShared.Geometry.BoundedHolderCore

/-! A native Hölder test on the manifold, read in a chart and multiplied by a
Lipschitz compactly supported coordinate weight `ζ` (supported in the chart
target), is a Euclidean Hölder function of the same order whose constant is a
fixed multiple of the native test constant. -/
public noncomputable section
set_option linter.unusedSectionVars false
namespace LeanShared.NativeChartTest
open Set Manifold Metric Bundle IsManifold
open scoped Topology Manifold ContDiff Bundle NNReal BoundedContinuousFunction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph M E) (ζ : E → ℂ)

/-- The chart reading of a function, weighted by `ζ` and extended by zero. -/
def reading (φ : M → ℂ) (y : E) : ℂ := by
  classical
  exact if y ∈ c.target then ζ y * φ (c.symm y) else 0

theorem reading_of_mem (φ : M → ℂ) {y : E} (hy : y ∈ c.target) :
    reading c ζ φ y = ζ y * φ (c.symm y) := by
  classical
  simp only [reading, hy, ↓reduceIte]

theorem reading_of_not_mem_tsupport (φ : M → ℂ) {y : E} (hy : y ∉ tsupport ζ) :
    reading c ζ φ y = 0 := by
  classical
  unfold reading
  split_ifs
  · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  · rfl

theorem reading_continuous (inside : tsupport ζ ⊆ c.target) (hζ : Continuous ζ)
    (φ : M → ℂ) (hφ : Continuous φ) : Continuous (reading c ζ φ) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ c.target
  · have nearby : reading c ζ φ =ᶠ[𝓝 y] fun z => ζ z * φ (c.symm z) :=
      Filter.eventually_of_mem (c.open_target.mem_nhds hy) fun z hz => reading_of_mem c ζ φ hz
    exact (hζ.continuousAt.mul (hφ.continuousAt.comp (c.continuousAt_symm hy))).congr nearby.symm
  · have hout : y ∉ tsupport ζ := fun h => hy (inside h)
    have nearby : reading c ζ φ =ᶠ[𝓝 y] fun _ => 0 :=
      Filter.eventually_of_mem ((isClosed_tsupport ζ).isOpen_compl.mem_nhds hout)
        fun z hz => reading_of_not_mem_tsupport c ζ φ hz
    exact continuousAt_const.congr nearby.symm

theorem reading_norm_le (φ : M → ℂ) {Z A : ℝ} (hZ : ∀ y, ‖ζ y‖ ≤ Z) (hA0 : 0 ≤ A)
    (hA : ∀ x, ‖φ x‖ ≤ A) (y : E) : ‖reading c ζ φ y‖ ≤ Z * A := by
  classical
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ y)
  unfold reading
  split_ifs
  · rw [norm_mul]
    exact mul_le_mul (hZ y) (hA _) (norm_nonneg _) hZ0
  · rw [norm_zero]
    exact mul_nonneg hZ0 hA0


theorem small_le_rpow {x b : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1) :
    x ≤ x ^ b := by
  by_cases hx : x = 0
  · subst hx; rw [Real.zero_rpow hb.ne']
  · have := Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne h0 (Ne.symm hx)) h1 hb1
    rwa [Real.rpow_one] at this

section Native
variable [FiniteDimensional ℝ E] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

/-- The chart reading of a native Hölder test is Hölder with a constant proportional
to the native constant. -/
theorem reading_holder (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (inside : tsupport ζ ⊆ c.target)
    (compactζ : HasCompactSupport ζ) {Λ : ℝ≥0} (lipζ : LipschitzWith Λ ζ)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (φ : M → ℂ) (A : ℝ), 0 ≤ A → (∀ x, ‖φ x‖ ≤ A) →
      (∀ x y, ‖φ x - φ y‖ ≤ A * dist x y ^ b) →
      ∀ y z, ‖reading c ζ φ y - reading c ζ φ z‖ ≤ H * A * ‖y - z‖ ^ b := by
  intro _
  obtain ⟨L, hL0, lipInv⟩ := BoundedRiemannianMetric.inverse_chart_compact (E := E) (M := M) c hc
    (tsupport ζ) compactζ inside
  obtain ⟨Z, hZ⟩ := (lipζ.continuous.norm.bddAbove_range_of_hasCompactSupport compactζ.norm)
  have hZy : ∀ y, ‖ζ y‖ ≤ Z := fun y => hZ ⟨y, rfl⟩
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZy 0)
  let H : ℝ := Z * L ^ b + Λ + 2 * Z
  have hLb : 0 ≤ L ^ b := Real.rpow_nonneg hL0 b
  refine ⟨H, by positivity, ?_⟩
  intro φ A hA0 hA holder y z
  have hd : 0 ≤ ‖y - z‖ := norm_nonneg _
  have hdb : 0 ≤ ‖y - z‖ ^ b := Real.rpow_nonneg hd b
  -- the two raw estimates
  have raw : ‖reading c ζ φ y - reading c ζ φ z‖ ≤
      Z * A * (L ^ b * ‖y - z‖ ^ b) + Λ * ‖y - z‖ * A := by
    have hLip : ‖ζ y - ζ z‖ ≤ Λ * ‖y - z‖ := by
      have := lipζ.dist_le_mul y z
      rwa [dist_eq_norm, dist_eq_norm] at this
    have hpos : 0 ≤ Z * A * (L ^ b * ‖y - z‖ ^ b) := by positivity
    by_cases hy : y ∈ tsupport ζ <;> by_cases hz : z ∈ tsupport ζ
    · rw [reading_of_mem c ζ φ (inside hy), reading_of_mem c ζ φ (inside hz)]
      have hdist : dist (c.symm y) (c.symm z) ^ b ≤ L ^ b * ‖y - z‖ ^ b := by
        rw [← Real.mul_rpow hL0 hd, ← dist_eq_norm]
        exact Real.rpow_le_rpow dist_nonneg (lipInv y hy z hz) hb.le
      have e : ζ y * φ (c.symm y) - ζ z * φ (c.symm z) =
          ζ y * (φ (c.symm y) - φ (c.symm z)) + (ζ y - ζ z) * φ (c.symm z) := by ring
      rw [e]
      calc ‖ζ y * (φ (c.symm y) - φ (c.symm z)) + (ζ y - ζ z) * φ (c.symm z)‖
          ≤ ‖ζ y‖ * ‖φ (c.symm y) - φ (c.symm z)‖ + ‖ζ y - ζ z‖ * ‖φ (c.symm z)‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ Z * (A * (L ^ b * ‖y - z‖ ^ b)) + Λ * ‖y - z‖ * A := by
            apply add_le_add
            · exact mul_le_mul (hZy y) ((holder _ _).trans
                (mul_le_mul_of_nonneg_left hdist hA0)) (norm_nonneg _) hZ0
            · exact mul_le_mul hLip (hA _) (norm_nonneg _) (by positivity)
        _ = Z * A * (L ^ b * ‖y - z‖ ^ b) + Λ * ‖y - z‖ * A := by ring
    · rw [reading_of_not_mem_tsupport c ζ φ hz, sub_zero, reading_of_mem c ζ φ (inside hy)]
      have hζz : ζ z = 0 := image_eq_zero_of_notMem_tsupport hz
      calc ‖ζ y * φ (c.symm y)‖ = ‖ζ y - ζ z‖ * ‖φ (c.symm y)‖ := by
            rw [hζz, sub_zero, norm_mul]
        _ ≤ Λ * ‖y - z‖ * A := mul_le_mul hLip (hA _) (norm_nonneg _) (by positivity)
        _ ≤ _ := le_add_of_nonneg_left hpos
    · rw [reading_of_not_mem_tsupport c ζ φ hy, zero_sub, norm_neg,
        reading_of_mem c ζ φ (inside hz)]
      have hζy : ζ y = 0 := image_eq_zero_of_notMem_tsupport hy
      calc ‖ζ z * φ (c.symm z)‖ = ‖ζ y - ζ z‖ * ‖φ (c.symm z)‖ := by
            rw [hζy, zero_sub, norm_neg, norm_mul]
        _ ≤ Λ * ‖y - z‖ * A := mul_le_mul hLip (hA _) (norm_nonneg _) (by positivity)
        _ ≤ _ := le_add_of_nonneg_left hpos
    · rw [reading_of_not_mem_tsupport c ζ φ hy, reading_of_not_mem_tsupport c ζ φ hz, sub_zero,
        norm_zero]
      positivity
  have bounded : ‖reading c ζ φ y - reading c ζ φ z‖ ≤ 2 * Z * A := by
    calc ‖reading c ζ φ y - reading c ζ φ z‖ ≤ ‖reading c ζ φ y‖ + ‖reading c ζ φ z‖ :=
          norm_sub_le _ _
      _ ≤ Z * A + Z * A := add_le_add (reading_norm_le c ζ φ hZy hA0 hA y)
          (reading_norm_le c ζ φ hZy hA0 hA z)
      _ = 2 * Z * A := by ring
  by_cases near : ‖y - z‖ ≤ 1
  · have hsmall := small_le_rpow hd near hb hb1
    calc ‖reading c ζ φ y - reading c ζ φ z‖
        ≤ Z * A * (L ^ b * ‖y - z‖ ^ b) + Λ * ‖y - z‖ * A := raw
      _ ≤ Z * A * (L ^ b * ‖y - z‖ ^ b) + Λ * ‖y - z‖ ^ b * A := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsmall (NNReal.coe_nonneg Λ)) hA0)
      _ ≤ H * A * ‖y - z‖ ^ b := by
          have : 0 ≤ 2 * Z * A * ‖y - z‖ ^ b := by positivity
          simp only [H]
          nlinarith
  · push Not at near
    have hge : 1 ≤ ‖y - z‖ ^ b := Real.one_le_rpow near.le hb.le
    calc ‖reading c ζ φ y - reading c ζ φ z‖ ≤ 2 * Z * A := bounded
      _ ≤ 2 * Z * A * ‖y - z‖ ^ b := le_mul_of_one_le_right (by positivity) hge
      _ ≤ H * A * ‖y - z‖ ^ b := by
          have : 0 ≤ (Z * L ^ b + Λ) * A * ‖y - z‖ ^ b := by positivity
          simp only [H]
          nlinarith

end Native

end LeanShared.NativeChartTest
