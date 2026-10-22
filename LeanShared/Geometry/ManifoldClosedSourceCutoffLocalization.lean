module
public import LeanShared.Geometry.ManifoldClosedCutoffHolderLocalization
public import LeanShared.Geometry.LittleHolderLinearPrecomposition
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! An additional source smooth cutoff changes the ordinary localization
constant while retaining the exact original native closed support. The
smaller cutoff support is included by the proved identity precomposition
operator, so no openness or extra boundary approximation is required. -/
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ManifoldClosedSourceCutoffLocalization
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  {S : Set M} (e : J → OpenPartialHomeomorph M E)
  (D : ConstructedManifoldLocalization.Data e S)
  (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V : Set M} (openV : IsOpen V) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (θ : M → ℂ) (smoothθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
  (compactθ : HasCompactSupport θ) (supportθ : tsupport θ ⊆ c.source)
  (χ : M → ℂ) (smoothχ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ χ)

def cutoff : M → ℂ := fun x => χ x * θ x

include smoothθ smoothχ in
omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem smooth_cutoff : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (cutoff θ χ) := by
  have multiply : ContMDiff (𝓘(ℝ, ℂ × ℂ)) (𝓘(ℝ, ℂ)) ∞
      (fun z : ℂ × ℂ => z.1 * z.2) :=
    (contDiff_mul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2)).contMDiff
  exact multiply.comp (smoothχ.prodMk_space smoothθ)

include supportθ in
omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [NormedSpace ℝ E] [ChartedSpace E M] in
theorem support_cutoff : tsupport (cutoff θ χ) ⊆ c.source :=
  tsupport_mul_subset_right.trans supportθ

include compactθ in
omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem compact_cutoff : HasCompactSupport (cutoff θ χ) :=
  compactθ.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
omit [ChartedSpace E M] in
theorem support_cover : (ContinuousLinearEquiv.refl ℝ E) '' ChartLocalization.localSupport c (cutoff θ χ) ⊆
    ChartLocalization.localSupport c θ := by
  change (id : E → E) '' _ ⊆ _
  rw [image_id]
  exact image_mono tsupport_mul_subset_right

def localization : ManifoldSmoothHolderCore.Lower e D openV hb hb1 →L[ℂ]
    EuclideanSmoothHolderCore.space
      (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).closure hb hb1 :=
  (LittleHolderLinearPrecomposition.operator (ContinuousLinearEquiv.refl ℝ E)
    (support_cover c θ χ) hb hb1
    (ChartLocalization.localSupport_isCompact c (cutoff θ χ)
      (support_cutoff c θ supportθ χ) (compact_cutoff θ compactθ χ)).closure
    (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).closure).comp
    (ManifoldClosedCutoffHolderLocalization.localization e D atlas openV hb hb1 c hc
      (cutoff θ χ) (smooth_cutoff θ smoothθ χ smoothχ) (compact_cutoff θ compactθ χ)
      (support_cutoff c θ supportθ χ))

omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem physical_localization (region : V ⊆ S)
    (v : ManifoldSmoothHolderCore.Lower e D openV hb hb1) (y : E) :
    EuclideanSmoothHolderCore.physical
      (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).closure hb hb1
      (localization e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ χ smoothχ v) y =
      ChartLocalization.coordinate c (cutoff θ χ) (ManifoldSmoothHolderCore.physical e D openV hb hb1 v) y := by
  rw [localization, ContinuousLinearMap.comp_apply, LittleHolderLinearPrecomposition.physical_operator]
  exact ManifoldClosedCutoffHolderLocalization.physical_localization e D atlas openV hb hb1
    c hc (cutoff θ χ) (smooth_cutoff θ smoothθ χ smoothχ) (compact_cutoff θ compactθ χ)
    (support_cutoff c θ supportθ χ) region v y

end LeanShared.ManifoldClosedSourceCutoffLocalization
