module
public import LeanShared.Geometry.CompactRiemannianChartBounds
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Operator.Banach

/-! The ordinary inverse function theorem gives actual open injectivity
neighborhoods from C1 manifold calculus and a bijective differential. -/
public noncomputable section
namespace LeanShared.ManifoldLocalInjectivity
open Set IsManifold
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 1600000 in
theorem exists_neighborhood_to_normed
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (f : M → F) (x : M) (smooth : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f x)
    (rank : Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x)) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ InjOn f U := by
  let c := chartAt E x
  have inside : x ∈ c.source := mem_chart_source E x
  have hc := CompactRiemannianChartBounds.chart_differentiable c (chart_mem_maximalAtlas x)
  let C := hc.mfderiv inside
  let input := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)).symm.trans C.symm
  let output := NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)
  let B := output.toContinuousLinearMap.comp
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x).comp input.toContinuousLinearMap)
  have bijectiveB : Function.Bijective B := output.bijective.comp (rank.comp input.bijective)
  let L := ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr bijectiveB.1) (LinearMap.range_eq_top.mpr bijectiveB.2)
  have first : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) c.symm (c x) C.symm.toContinuousLinearMap :=
    (hc.mdifferentiableAt_symm (c.map_source inside)).hasMFDerivAt
  have second : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,F)) f (c.symm (c x))
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x) := by
    rw [c.left_inv inside]
    exact (smooth.mdifferentiableAt one_ne_zero).hasMFDerivAt
  have derivative : HasFDerivAt (f ∘ c.symm) L.toContinuousLinearMap (c x) :=
    (second.comp (c x) first).hasFDerivAt
  have sourceSmooth : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 c.symm (c x) :=
    (contMDiffAt_symm_of_mem_maximalAtlas
      (chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) x) (c.map_source inside)).of_le (by decide)
  have smoothG : ContDiffAt ℝ 1 (f ∘ c.symm) (c x) := by
    have middle : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f (c.symm (c x)) := by
      rw [c.left_inv inside]
      exact smooth
    exact (middle.comp (c x) sourceSmooth).contDiffAt
  let h := smoothG.toOpenPartialHomeomorph (f ∘ c.symm) derivative one_ne_zero
  have member : c x ∈ h.source := smoothG.mem_toOpenPartialHomeomorph_source derivative one_ne_zero
  let U := c.source ∩ c ⁻¹' h.source
  refine ⟨U,c.continuousOn.isOpen_inter_preimage c.open_source h.open_source,⟨inside,member⟩,?_⟩
  intro y hy z hz equal
  apply c.injOn hy.1 hz.1
  apply h.injOn hy.2 hz.2
  change f (c.symm (c y)) = f (c.symm (c z))
  rw [c.left_inv hy.1,c.left_inv hz.1,equal]

set_option maxHeartbeats 1600000 in
theorem exists_neighborhood
    {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ,F)) ∞ N]
    (f : M → N) (x : M) (smooth : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f x)
    (rank : Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x)) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ InjOn f U := by
  let d := chartAt F (f x)
  have target : f x ∈ d.source := mem_chart_source F (f x)
  have hd := CompactRiemannianChartBounds.chart_differentiable d (chart_mem_maximalAtlas (f x))
  have chartSmooth : ContMDiffAt (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 d (f x) :=
    (contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (I := 𝓘(ℝ,F)) (n := ∞) (f x)) target).of_le (by decide)
  have composite := chartSmooth.comp x smooth
  have rankComposite : Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) (d ∘ f) x) := by
    rw [mfderiv_comp x (chartSmooth.mdifferentiableAt one_ne_zero) (smooth.mdifferentiableAt one_ne_zero)]
    exact (hd.mfderiv target).bijective.comp rank
  obtain ⟨U,openU,member,injective⟩ := exists_neighborhood_to_normed (d ∘ f) x composite rankComposite
  exact ⟨U,openU,member,fun y hy z hz equal => injective hy hz (congrArg d equal)⟩

end LeanShared.ManifoldLocalInjectivity
