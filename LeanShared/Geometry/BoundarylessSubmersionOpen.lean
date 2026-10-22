module
public import LeanShared.Geometry.SubmersionOpen
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-! Full-rank C1 maps between boundaryless manifolds are locally open,
derived through actual charts and the Banach inverse function theorem. -/
public section
open Set Filter IsManifold
open scoped Topology ContDiff Manifold
namespace LeanShared.SubmersionOpen

theorem map_nhds_eq_of_mfderiv_surjective_boundaryless
    {E F HM HN M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace HM] [TopologicalSpace HN]
    {I : ModelWithCorners ℝ E HM} {J : ModelWithCorners ℝ F HN}
    [I.Boundaryless] [J.Boundaryless]
    [TopologicalSpace M] [ChartedSpace HM M]
    [TopologicalSpace N] [ChartedSpace HN N]
    {f : M → N} {x : M}
    (smooth : ContMDiffAt I J 1 f x)
    (rank : Function.Surjective (mfderiv I J f x)) :
    Filter.map f (𝓝 x) = 𝓝 (f x) := by
  let a := extChartAt I x
  let b := extChartAt J (f x)
  let g := writtenInExtChartAt I J x f
  have cd : ContDiffAt ℝ 1 g (a x) := by
    have within : ContDiffWithinAt ℝ 1 g univ (a x) := by
      simpa [g, a, writtenInExtChartAt, I.range_eq_univ] using (contMDiffAt_iff.mp smooth).2
    exact within.contDiffAt Filter.univ_mem
  have md := smooth.mdifferentiableAt one_ne_zero
  have derivative : mfderiv I J f x = fderiv ℝ g (a x) := by
    simpa [g, a, I.range_eq_univ] using md.mfderiv_abuse
  have full : Function.Surjective (fderiv ℝ g (a x)) := by rwa [← derivative]
  have value : g (a x) = b (f x) := by simp only [g, a, b, mfld_simps]
  have inverse : (fun z => b.symm (g (a z))) =ᶠ[𝓝 x] f := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x,
      smooth.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := J) (f x))]
      with z hz hfz
    change b.symm (b (f (a.symm (a z)))) = f z
    rw [a.left_inv hz, b.left_inv hfz]
  calc
    Filter.map f (𝓝 x) = Filter.map b.symm (Filter.map g (Filter.map a (𝓝 x))) := by
      rw [Filter.map_map, Filter.map_map]
      exact Filter.map_congr inverse.symm
    _ = Filter.map b.symm (𝓝 (b (f x))) := by
      rw [show Filter.map a (𝓝 x) = 𝓝 (a x) from
        map_extChartAt_nhds_of_boundaryless x, map_nhds_eq cd full, value]
    _ = 𝓝 (f x) := by
      simpa [b, J.range_eq_univ]
        using (map_extChartAt_symm_nhdsWithin_range (I := J) (f x))

/-- Full differential rank on an open set implies its image is open. -/
theorem isOpen_image_of_mfderiv_surjective_boundaryless
    {E F HM HN M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace HM] [TopologicalSpace HN]
    {I : ModelWithCorners ℝ E HM} {J : ModelWithCorners ℝ F HN}
    [I.Boundaryless] [J.Boundaryless]
    [TopologicalSpace M] [ChartedSpace HM M]
    [TopologicalSpace N] [ChartedSpace HN N]
    {f : M → N} {s : Set M} (hs : IsOpen s)
    (smooth : ∀ x ∈ s, ContMDiffAt I J 1 f x)
    (rank : ∀ x ∈ s, Function.Surjective (mfderiv I J f x)) :
    IsOpen (f '' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  have h := Filter.image_mem_map (m := f) (hs.mem_nhds hx)
  rwa [map_nhds_eq_of_mfderiv_surjective_boundaryless (smooth x hx) (rank x hx)] at h
end LeanShared.SubmersionOpen
