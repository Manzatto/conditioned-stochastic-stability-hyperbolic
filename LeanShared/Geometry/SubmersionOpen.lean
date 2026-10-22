module
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Genuine differential submersions are open. These results derive
neighbourhood surjectivity from the inverse function theorem; openness and
control-image coverage are conclusions rather than background inputs. -/
public section
open Set Filter
open scoped Topology ContDiff
namespace LeanShared.SubmersionOpen

/-- A C1 map with surjective derivative maps the full neighbourhood filter
onto the neighbourhood filter of its value. -/
theorem map_nhds_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {x : E} (smooth : ContDiffAt ℝ 1 f x)
    (rank : Function.Surjective (fderiv ℝ f x)) :
    Filter.map f (𝓝 x) = 𝓝 (f x) :=
  (smooth.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr rank)

/-- The image of any open region where a C1 map has full rank is open. -/
theorem isOpen_image
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {s : Set E} (hs : IsOpen s)
    (smooth : ∀ x ∈ s, ContDiffAt ℝ 1 f x)
    (rank : ∀ x ∈ s, Function.Surjective (fderiv ℝ f x)) : IsOpen (f '' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  have h := Filter.image_mem_map (m := f) (hs.mem_nhds hx)
  rwa [map_nhds_eq (smooth x hx) (rank x hx)] at h
end LeanShared.SubmersionOpen
