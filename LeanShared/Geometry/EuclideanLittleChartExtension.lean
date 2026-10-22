module
public import LeanShared.Geometry.EuclideanFractionalLowerSpace
public import LeanShared.Geometry.SupportedHolderChartSpace

/-! The actual supported Euclidean little Hölder completion embeds in
the fixed compact chart-supported graph and therefore has a constructed
global manifold realization. Boundary support is controlled by closure W;
no false assertion of support strictly inside W for every limit is made. -/
public noncomputable section
open Set
open scoped BoundedContinuousFunction Manifold ContDiff
namespace LeanShared.EuclideanLittleChartExtension
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  {W : Set E} (compact : IsCompact (closure W)) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)

include compact in
theorem zero_outside_closure (v : EuclideanSmoothHolderCore.space compact hb hb1)
    (y : E) (hy : y ∉ closure W) : EuclideanSmoothHolderCore.physical compact hb hb1 v y = 0 := by
  apply (EuclideanSmoothHolderCore.smooth_dense compact hb hb1).induction_on
    (p := fun z => EuclideanSmoothHolderCore.physical compact hb hb1 z y = 0) v
    (isClosed_eq ((BoundedContinuousFunction.evalCLM ℂ y).continuous.comp
      (EuclideanSmoothHolderCore.physical compact hb hb1).continuous) continuous_const)
  intro c
  exact SmoothSupportedManifoldCore.zero_outside W c y (fun hw => hy (subset_closure hw))

@[expose] def supported : EuclideanSmoothHolderCore.space compact hb hb1 →L[ℂ]
    SupportedHolderChartSpace.space (a := b) (closure W) :=
  (EuclideanSmoothHolderCore.space compact hb hb1).subtypeL.codRestrict
    (SupportedHolderChartSpace.space (a := b) (closure W))
    (fun v y hy => zero_outside_closure compact hb hb1 v y hy)

variable (e : OpenPartialHomeomorph M E) (inside : closure W ⊆ e.target)

@[expose] def realization : EuclideanSmoothHolderCore.space compact hb hb1 →L[ℂ] (M →ᵇ ℂ) :=
  (SupportedHolderChartSpace.realization compact e inside).comp (supported compact hb hb1)

omit [ChartedSpace E M] in
theorem realization_apply (v : EuclideanSmoothHolderCore.space compact hb hb1) (x : M) :
    realization compact hb hb1 e inside v x =
      SupportedChartExtension.function e (fun y => EuclideanSmoothHolderCore.physical compact hb hb1 v y) x := rfl

omit [ChartedSpace E M] in
theorem realization_norm (v : EuclideanSmoothHolderCore.space compact hb hb1) :
    ‖realization compact hb hb1 e inside v‖ ≤ ‖v‖ := by
  exact SupportedHolderChartSpace.norm_physical compact e inside (supported compact hb hb1 v)

theorem realization_regular [IsManifold (𝓘(ℝ,E)) ∞ M]
    (he : e ∈ IsManifold.maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (v : EuclideanSmoothHolderCore.space compact hb hb1) :
    FractionalManifoldRegularity.Regular (E := E) (F := ℂ) b
      (fun x => realization compact hb hb1 e inside v x) :=
  SupportedHolderChartSpace.realization_regular compact e inside he hb hb1
    (supported compact hb hb1 v)
end LeanShared.EuclideanLittleChartExtension
