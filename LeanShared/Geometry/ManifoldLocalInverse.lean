module
public import LeanShared.Geometry.ManifoldLocalLeftInverse
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! The actual local inverse between boundaryless manifolds is C1 from
bijectivity of the actual differential; inverse regularity is not assumed. -/
public noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.ManifoldLocalInverse

theorem contMDiffAt_of_eventually_leftInverse
    {E F M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ,F)) 1 N]
    {f : M → N} {g : N → M} {x : M}
    (smooth : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f x)
    (rank : Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x))
    (inverse : ∀ᶠ z in 𝓝 x, g (f z)=z) :
    ContMDiffAt (𝓘(ℝ,F)) (𝓘(ℝ,E)) 1 g (f x) := by
  let d := chartAt F (f x)
  have member : f x ∈ d.source := mem_chart_source F (f x)
  have chartSmooth : ContMDiffAt (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 d (f x) :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (f x)) member
  have forward : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 (d ∘ f) x :=
    chartSmooth.comp x smooth
  have bijective : Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) (d ∘ f) x) := by
    rw [mfderiv_comp x (chartSmooth.mdifferentiableAt one_ne_zero)
      (smooth.mdifferentiableAt one_ne_zero)]
    exact ((mdifferentiable_chart (I := 𝓘(ℝ,F)) (f x)).mfderiv_bijective member).comp rank
  have left : ∀ᶠ z in 𝓝 x, (g ∘ d.symm) ((d ∘ f) z)=z := by
    filter_upwards [inverse, smooth.continuousAt.eventually (chart_source_mem_nhds F (f x))]
      with z hz memberZ
    change g (d.symm (d (f z)))=z
    rw [d.left_inv memberZ,hz]
  have localInverse := ManifoldLocalLeftInverse.contMDiffAt_of_eventually_leftInverse forward bijective left
  have composition : ContMDiffAt (𝓘(ℝ,F)) (𝓘(ℝ,E)) 1 ((g ∘ d.symm) ∘ d) (f x) :=
    localInverse.comp (f x) chartSmooth
  apply composition.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds F (f x)] with y hy
  change g y=g (d.symm (d y))
  rw [d.left_inv hy]
end LeanShared.ManifoldLocalInverse
