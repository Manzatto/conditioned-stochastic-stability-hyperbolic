module
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! Literal manifold control rank yields C1, full-control-rank maps in actual
state and target atlas charts. No coordinate regularity or rank is supplied. -/
public section
namespace LeanShared.ControlSubmersionCoordinates
open Set Filter IsManifold
open scoped Topology ContDiff Manifold

theorem chart_contDiffAt
    {E A M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
    {H : M × A → M} {x : M} {a : A}
    (smooth : ContMDiffAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, E)) 1 H (x, a)) :
    ContDiffAt ℝ 1 (fun z : E × A =>
      (chartAt E (H (x, a))) (H (Prod.map (chartAt E x).symm id z))) ((chartAt E x) x, a) := by
  let c := chartAt E x
  let d := chartAt E (H (x, a))
  have cx : x ∈ c.source := mem_chart_source E x
  have inverse : c.symm (c x) = x := c.left_inv cx
  have inverseSmooth : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 c.symm (c x) :=
    contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas x) (c.map_source cx)
  have inner := inverseSmooth.prodMap (contMDiffAt_id (I := 𝓘(ℝ, A)) (x := a))
  have smoothAt : ContMDiffAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, E)) 1
      H (c.symm (c x), a) := by simpa only [inverse] using smooth
  have composed := smoothAt.comp (c x, a) inner
  have dx : H (x, a) ∈ d.source := mem_chart_source E (H (x, a))
  have outerSmooth : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 d (H (c.symm (c x), a)) := by
    rw [inverse]
    exact contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (H (x, a))) dx
  have result := outerSmooth.comp (c x, a) composed
  have within : ContDiffWithinAt ℝ 1 (fun z : E × A =>
      (chartAt E (H (x, a))) (H (Prod.map (chartAt E x).symm id z))) univ
      ((chartAt E x) x, a) := by
    simpa [writtenInExtChartAt, c, d, chartAt_self_eq, Function.comp_def, Prod.map_apply, mfld_simps]
      using (contMDiffAt_iff.mp result).2
  exact within.contDiffAt Filter.univ_mem

theorem chart_control_fderiv_surjective
    {E A M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
    {H : M × A → M} {x : M} {a : A}
    (smooth : ContMDiffAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, E)) 1 H (x, a))
    (rank : Function.Surjective (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) (fun b => H (x, b)) a)) :
    Function.Surjective (fderiv ℝ (fun b =>
      (chartAt E (H (x, a))) (H ((chartAt E x).symm ((chartAt E x) x), b))) a) := by
  have partialSmooth := smooth.comp a
    (contMDiffAt_const.prodMk (contMDiffAt_id (I := 𝓘(ℝ, A)) (x := a)))
  change Function.Surjective (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) (H ∘ Prod.mk x) a) at rank
  rw [(partialSmooth.mdifferentiableAt one_ne_zero).mfderiv] at rank
  intro y
  obtain ⟨b, hb⟩ := rank ((tangentSpaceCastModel (𝓘(ℝ, E)) (H (x, a))).symm y)
  refine ⟨tangentSpaceCastModel (𝓘(ℝ, A)) a b, ?_⟩
  have equality := congrArg (tangentSpaceCastModel (𝓘(ℝ, E)) (H (x, a))) hb
  simpa [writtenInExtChartAt, chartAt_self_eq, Function.comp_def, mfld_simps] using equality

end LeanShared.ControlSubmersionCoordinates
