module
public import LeanShared.Analysis.DerivativeChordComparison
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-! Chord bounds pass to tangent maps in actual boundaryless charts. -/
public section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.DerivativeChordComparison

theorem norm_mfderiv_apply_le_of_chord
    {E F G M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M]
    {f : M → F} {g : M → G} {x : M} {C : ℝ}
    (hf : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) 1 f x)
    (hg : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, G)) 1 g x)
    (chord : ∀ᶠ z in 𝓝 x, ‖f z - f x‖ ≤ C * ‖g z - g x‖)
    (v : E) :
    ‖mvfderiv (𝓘(ℝ, E)) f x v‖ ≤
      C * ‖mvfderiv (𝓘(ℝ, E)) g x v‖ := by
  let a := extChartAt (𝓘(ℝ, E)) x
  let fc := writtenInExtChartAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) x f
  let gc := writtenInExtChartAt (𝓘(ℝ, E)) (𝓘(ℝ, G)) x g
  have fd : ContDiffAt ℝ 1 fc (a x) := by
    have h : ContDiffWithinAt ℝ 1 fc univ (a x) := by
      simpa [fc, a, writtenInExtChartAt] using (contMDiffAt_iff.mp hf).2
    exact h.contDiffAt Filter.univ_mem
  have gd : ContDiffAt ℝ 1 gc (a x) := by
    have h : ContDiffWithinAt ℝ 1 gc univ (a x) := by
      simpa [gc, a, writtenInExtChartAt] using (contMDiffAt_iff.mp hg).2
    exact h.contDiffAt Filter.univ_mem
  have df : mvfderiv (𝓘(ℝ, E)) f x = fderiv ℝ fc (a x) := by
    simpa [fc, a] using (hf.mdifferentiableAt one_ne_zero).mvfderiv
  have dg : mvfderiv (𝓘(ℝ, E)) g x = fderiv ℝ gc (a x) := by
    simpa [gc, a] using (hg.mdifferentiableAt one_ne_zero).mvfderiv
  rw [df, dg]
  apply norm_fderiv_apply_le_of_chord
    (fd.differentiableAt one_ne_zero).hasFDerivAt
    (gd.differentiableAt one_ne_zero).hasFDerivAt
  have inverse : Tendsto a.symm (𝓝 (a x)) (𝓝 x) := by
    have h := map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℝ, E)) x
    have h' : Filter.map a.symm (𝓝 (a x)) = 𝓝 x := by
      simpa only [a, mfld_simps, nhdsWithin_univ] using h
    exact le_of_eq h'
  filter_upwards [inverse.eventually chord] with z hz
  change ‖f (a.symm z) - f (a.symm (a x))‖ ≤ C * ‖g (a.symm z) - g (a.symm (a x))‖
  rw [a.left_inv (mem_extChartAt_source (I := 𝓘(ℝ, E)) x)]
  exact hz
end LeanShared.DerivativeChordComparison
