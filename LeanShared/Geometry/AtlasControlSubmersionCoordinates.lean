module
public import LeanShared.Geometry.ControlSubmersionCoordinates
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Actual coordinates and full control rank in an arbitrary smooth atlas
chart. This permits a finite, constructed volume reference instead of an
assumed measure comparison in every canonical chart. -/
public section
namespace LeanShared.ControlSubmersionCoordinates
open Set Filter IsManifold
open scoped Topology ContDiff Manifold

theorem atlas_chart_contDiffAt
    {E A M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
    {H : M × A → M} {x : M} {a : A}
    (smooth : ContMDiffAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, E)) 1 H (x, a))
    (e : OpenPartialHomeomorph M E) (atlas : e ∈ maximalAtlas (𝓘(ℝ, E)) 1 M)
    (source : H (x, a) ∈ e.source) :
    ContDiffAt ℝ 1 (fun z : E × A =>
      e (H (Prod.map (chartAt E x).symm id z))) ((chartAt E x) x, a) := by
  let c := chartAt E x
  have cx : x ∈ c.source := mem_chart_source E x
  have inverse : c.symm (c x) = x := c.left_inv cx
  have inverseSmooth : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 c.symm (c x) :=
    contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas x) (c.map_source cx)
  have inner := inverseSmooth.prodMap (contMDiffAt_id (I := 𝓘(ℝ, A)) (x := a))
  have smoothAt : ContMDiffAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, E)) 1
      H (c.symm (c x), a) := by simpa only [inverse] using smooth
  have composed := smoothAt.comp (c x, a) inner
  have outerSmooth : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 e (H (c.symm (c x), a)) := by
    rw [inverse]
    exact contMDiffAt_of_mem_maximalAtlas atlas source
  have result := outerSmooth.comp (c x, a) composed
  have within : ContDiffWithinAt ℝ 1 (fun z : E × A =>
      e (H (Prod.map (chartAt E x).symm id z))) univ ((chartAt E x) x, a) := by
    simpa [writtenInExtChartAt, c, chartAt_self_eq, Function.comp_def, mfld_simps]
      using (contMDiffAt_iff.mp result).2
  exact within.contDiffAt Filter.univ_mem

theorem atlas_chart_control_fderiv_surjective
    {E A M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
    {H : M × A → M} {x : M} {a : A}
    (smooth : ContMDiffAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, E)) 1 H (x, a))
    (rank : Function.Surjective (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) (fun b => H (x, b)) a))
    (e : OpenPartialHomeomorph M E) (atlas : e ∈ maximalAtlas (𝓘(ℝ, E)) 1 M)
    (source : H (x, a) ∈ e.source) :
    Function.Surjective (fderiv ℝ (fun b =>
      e (H ((chartAt E x).symm ((chartAt E x) x), b))) a) := by
  have partialSmooth := smooth.comp a
    (contMDiffAt_const.prodMk (contMDiffAt_id (I := 𝓘(ℝ, A)) (x := a)))
  have eDifferentiable : e.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) :=
    ⟨fun _ hp => (mdifferentiableAt_of_mem_maximalAtlas atlas hp).mdifferentiableWithinAt,
      fun _ hp => (mdifferentiableAt_symm_of_mem_maximalAtlas atlas hp).mdifferentiableWithinAt⟩
  have composedSmooth := (contMDiffAt_of_mem_maximalAtlas atlas source).comp a partialSmooth
  have composedRank : Function.Surjective
      (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) (e ∘ H ∘ Prod.mk x) a) := by
    rw [mfderiv_comp a (eDifferentiable.mdifferentiableAt source)
      (partialSmooth.mdifferentiableAt one_ne_zero)]
    exact (eDifferentiable.mfderiv_bijective source).2.comp rank
  rw [(composedSmooth.mdifferentiableAt one_ne_zero).mfderiv] at composedRank
  intro y
  obtain ⟨b, hb⟩ := composedRank ((tangentSpaceCastModel (𝓘(ℝ, E)) (e (H (x, a)))).symm y)
  refine ⟨tangentSpaceCastModel (𝓘(ℝ, A)) a b, ?_⟩
  have equality := congrArg (tangentSpaceCastModel (𝓘(ℝ, E)) (e (H (x, a)))) hb
  simpa [writtenInExtChartAt, chartAt_self_eq, Function.comp_def, mfld_simps] using equality

end LeanShared.ControlSubmersionCoordinates
