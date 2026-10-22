module
public import LeanShared.Geometry.ChartFiniteRegularLocalization
public import LeanShared.Geometry.ChartFractionalLocalization
public import LeanShared.Geometry.EuclideanAnyOrderHolderRealization

/-! Actual rough chart coordinates in the constructed lower space for every input u>b. -/
public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ChartAnyOrderHolderRealization
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (θ : M → ℂ) (support : tsupport θ ⊆ e.source) (compact : HasCompactSupport θ)
  (hθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
  {f : M → ℂ} {u b : ℝ} (hb : 0 < b) (hb1 : b < 1) (hbu : b < u)
  (hf : FractionalManifoldRegularity.Regular (E := E) (F := ℂ) u f)
  {W : Set E} (hW : IsCompact (closure W)) (openW : IsOpen W)
  (region : tsupport (ChartLocalization.coordinate e θ f) ⊆ W)

include μ he hb hb1 hbu openW region in
theorem exists_lower : ∃ v : EuclideanSmoothHolderCore.space hW hb hb1,
    EuclideanSmoothHolderCore.physical hW hb hb1 v =
      ChartFractionalLocalization.bounded e θ support compact hθ hf := by
  let h := ChartFractionalLocalization.bounded e θ support compact hθ hf
  have compactH : HasCompactSupport h := ChartLocalization.coordinate_hasCompactSupport e θ support compact f
  by_cases hu : u < 1
  · exact EuclideanSmoothHolderCore.exists_lower_of_any_regular μ hW hb hb1 h openW region compactH hbu
      (ChartFractionalLocalization.regular e θ support compact he hθ (hb.trans hbu) hu hf)
  · have floor : 1 ≤ ⌊u⌋₊ := (Nat.one_le_floor_iff u).mpr (le_of_not_gt hu)
    have f1 : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) 1 f := hf.differentiable.of_le (by exact_mod_cast floor)
    have local1 : ContDiff ℝ 1 (ChartLocalization.coordinate e θ f) :=
      ChartLocalization.coordinate_contDiff_of_order e θ support he hθ compact f1
    have regular1 : FractionalManifoldRegularity.Regular (E := E) (F := ℂ) 1 (fun x => h x) := by
      refine ⟨zero_le_one, ?_, ?_⟩
      · change ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) (⌊(1 : ℝ)⌋₊ : ℕ)
          (ChartLocalization.coordinate e θ f)
        simpa only [Nat.floor_one, Nat.cast_one] using local1.contMDiff
      · intro unequal
        exact False.elim (unequal (by norm_num))
    exact EuclideanSmoothHolderCore.exists_lower_of_any_regular μ hW hb hb1 h openW region compactH hb1 regular1
end LeanShared.ChartAnyOrderHolderRealization
