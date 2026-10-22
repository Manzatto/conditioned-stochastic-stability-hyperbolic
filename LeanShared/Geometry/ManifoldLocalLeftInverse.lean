module
public import LeanShared.Analysis.ContDiffLocalLeftInverse
public import LeanShared.Geometry.ManifoldSubmersionOpen
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! The actual local inverse is C¹ when the forward differential is bijective.
The inverse is not supplied any continuity or differentiability assumption. -/
public noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.ManifoldLocalLeftInverse

theorem contMDiffAt_of_eventually_leftInverse
    {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace M] [ChartedSpace E M]
    {f : M → F} {g : F → M} {x : M}
    (hf : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) 1 f x)
    (rank : Function.Bijective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x))
    (inverse : ∀ᶠ z in 𝓝 x, g (f z) = z) :
    ContMDiffAt (𝓘(ℝ, F)) (𝓘(ℝ, E)) 1 g (f x) := by
  have value : g (f x) = x := inverse.self_of_nhds
  have gc : ContinuousAt g (f x) := by
    rw [ContinuousAt, value]
    rw [← SubmersionOpen.map_nhds_eq_of_mfderiv_surjective hf rank.2]
    change Tendsto (g ∘ f) (𝓝 x) (𝓝 x)
    apply tendsto_id.congr'
    filter_upwards [inverse] with z hz
    exact hz.symm
  let a := extChartAt (𝓘(ℝ, E)) x
  let fc := writtenInExtChartAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) x f
  have fd : ContDiffAt ℝ 1 fc (a x) := by
    have h : ContDiffWithinAt ℝ 1 fc univ (a x) := by
      simpa [fc, a, writtenInExtChartAt] using (contMDiffAt_iff.mp hf).2
    exact h.contDiffAt Filter.univ_mem
  have derivative : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x = fderiv ℝ fc (a x) := by
    simpa [fc, a] using (hf.mdifferentiableAt one_ne_zero).mfderiv_abuse
  have bijective : Function.Bijective (fderiv ℝ fc (a x)) := by
    rwa [← derivative]
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ fc (a x))
    (LinearMap.ker_eq_bot.mpr bijective.1) (LinearMap.range_eq_top.mpr bijective.2)
  have fderivative : HasFDerivAt fc (L : E →L[ℝ] F) (a x) :=
    (fd.differentiableAt one_ne_zero).hasFDerivAt
  have chartInverse : Tendsto a.symm (𝓝 (a x)) (𝓝 x) := by
    have h := map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℝ, E)) x
    have h' : Filter.map a.symm (𝓝 (a x)) = 𝓝 x := by
      simpa only [a, mfld_simps, nhdsWithin_univ] using h
    exact le_of_eq h'
  have left : ∀ᶠ z in 𝓝 (a x), (a ∘ g) (fc z) = z := by
    filter_upwards [chartInverse.eventually inverse,
      extChartAt_target_mem_nhds (I := 𝓘(ℝ, E)) x]
      with z hz hz'
    change a (g (f (a.symm z))) = z
    rw [hz, a.right_inv hz']
  have regular := ContDiffLocalLeftInverse.contDiffAt_of_eventually_leftInverse
    fd fderivative one_ne_zero left
  have fx : fc (a x) = f x := by
    change f (a.symm (a x)) = f x
    rw [a.left_inv (mem_extChartAt_source (I := 𝓘(ℝ, E)) x)]
  apply contMDiffAt_iff.mpr
  refine ⟨gc, ?_⟩
  rw [fx] at regular
  rw [value]
  rw [extChartAt_model_space_eq_id ℝ (f x)]
  change ContDiffWithinAt ℝ 1 (a ∘ g) (range (𝓘(ℝ, F))) (f x)
  have rangeSelf : range (𝓘(ℝ, F)) = (univ : Set F) := by simp only [mfld_simps]
  rw [rangeSelf]
  exact regular.contDiffWithinAt
end LeanShared.ManifoldLocalLeftInverse
