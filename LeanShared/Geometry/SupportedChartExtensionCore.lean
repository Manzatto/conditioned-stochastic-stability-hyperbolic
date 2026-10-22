module
public import LeanShared.Geometry.SupportedChartExtension
public import LeanShared.Geometry.SmoothSupportedManifoldCore
public import LeanShared.Analysis.SchwartzJetSpace

/-! Zero extension of chart-supported Schwartz functions as a linear map into the smooth
supported manifold core. The support set is compact inside the chart target and its inverse
image lies in the region. -/
@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold
open scoped Manifold ContDiff SchwartzMap
attribute [local instance] Classical.propDecidable
namespace LeanShared.SupportedChartExtension

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  {D : Set E} (compact : IsCompact D) (inside : D ⊆ e.target) {V : Set M}
  (region : e.symm '' D ⊆ V)

omit [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [IsManifold (𝓘(ℝ, E)) ∞ M] in
include compact in
theorem supported_tsupport (f : SchwartzJetSpace.supportedCore D) : tsupport (f.val : E → ℂ) ⊆ D :=
  closure_minimal (fun x hx => by
    by_contra outside
    exact hx (f.property x outside)) compact.isClosed

include he compact inside region in
/-- The zero extension, as a linear map into the smooth supported core. -/
def coreMap : SchwartzJetSpace.supportedCore D →ₗ[ℂ] SmoothSupportedManifoldCore.core (E := E) V where
  toFun f := ⟨function e f.val,
    smooth e he (f.val.smooth ⊤)
      (compact.of_isClosed_subset (isClosed_tsupport _) (supported_tsupport compact f))
      ((supported_tsupport compact f).trans inside),
    (support_subset e (compact.of_isClosed_subset (isClosed_tsupport _)
      (supported_tsupport compact f)) ((supported_tsupport compact f).trans inside)).trans
      ((image_mono (supported_tsupport compact f)).trans region)⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    change function e (f + g).val x = function e f.val x + function e g.val x
    simp only [function]
    split_ifs <;> simp
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change function e (c • f).val x = c • function e f.val x
    simp only [function]
    split_ifs <;> simp

theorem coreMap_apply (f : SchwartzJetSpace.supportedCore D) (x : M) :
    SmoothSupportedManifoldCore.functions V (coreMap e he compact inside region f) x =
      if x ∈ e.source then f.val (e x) else 0 := rfl

end LeanShared.SupportedChartExtension
