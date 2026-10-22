module
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! Centered coordinates constructed from actual charts and actual tangent
frames. The derivative at the origin is the actual manifold differential
conjugated by those frames, rather than an assumed coordinate cocycle. -/
public noncomputable section
namespace LeanShared.CenteredManifoldCoordinates
open Set IsManifold
open scoped Manifold Topology

@[expose] def centered
    {P Q E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F) (a : E) (b : F) (h : E → F) : P → Q :=
  fun z => R.symm (h (a + L z) - b)

theorem centered_hasFDerivAt
    {P Q E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F) (a : E) (b : F) (h : E → F)
    (D : E →L[ℝ] F) (derivative : HasFDerivAt h D a) :
    HasFDerivAt (centered L R a b h)
      (R.symm.toContinuousLinearMap.comp (D.comp L.toContinuousLinearMap)) 0 := by
  have source : HasFDerivAt (fun z : P => a + L z) L.toContinuousLinearMap 0 := by
    simpa only [zero_add] using (L.hasFDerivAt : HasFDerivAt L L.toContinuousLinearMap (0 : P)).const_add a
  have at_source : HasFDerivAt h D (a + L (0 : P)) := by
    simpa only [_root_.map_zero, add_zero] using derivative
  have middle := (at_source.comp (0 : P) source).sub_const b
  exact R.symm.hasFDerivAt.comp (0 : P) middle

@[expose] def map
    {E F P Q M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (H : M → N) (x : M)
    (e : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (f : Q ≃L[ℝ] TangentSpace (𝓘(ℝ, F)) (H x)) : P → Q :=
  centered (e.trans (tangentSpaceCastModel (𝓘(ℝ, E)) x))
    (f.trans (tangentSpaceCastModel (𝓘(ℝ, F)) (H x)))
    (extChartAt (𝓘(ℝ, E)) x x) (extChartAt (𝓘(ℝ, F)) (H x) (H x))
    (writtenInExtChartAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) x H)

theorem map_zero
    {E F P Q M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (H : M → N) (x : M)
    (e : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (f : Q ≃L[ℝ] TangentSpace (𝓘(ℝ, F)) (H x)) : map H x e f 0 = 0 := by
  simp only [map, centered, _root_.map_zero, add_zero, writtenInExtChartAt, Function.comp_apply]
  rw [(extChartAt (𝓘(ℝ, E)) x).left_inv (mem_extChartAt_source x), sub_self, _root_.map_zero]

theorem map_hasFDerivAt
    {E F P Q M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (H : M → N) (x : M)
    (e : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (f : Q ≃L[ℝ] TangentSpace (𝓘(ℝ, F)) (H x))
    (smooth : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) H x) :
    HasFDerivAt (map H x e f)
      (f.symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) H x).comp e.toContinuousLinearMap)) 0 := by
  have differentiable := smooth.differentiableWithinAt_writtenInExtChartAt
  have derivative : HasFDerivAt (writtenInExtChartAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) x H)
      (fderiv ℝ (writtenInExtChartAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) x H)
        (extChartAt (𝓘(ℝ, E)) x x)) (extChartAt (𝓘(ℝ, E)) x x) := by
    exact (differentiable.differentiableAt (by simp only [mfld_simps]; exact Filter.univ_mem)).hasFDerivAt
  have result := centered_hasFDerivAt
    (e.trans (tangentSpaceCastModel (𝓘(ℝ, E)) x))
    (f.trans (tangentSpaceCastModel (𝓘(ℝ, F)) (H x)))
    (extChartAt (𝓘(ℝ, E)) x x) (extChartAt (𝓘(ℝ, F)) (H x) (H x))
    _ _ derivative
  have differential := smooth.mfderiv
  simp only [mfld_simps, fderivWithin_univ] at differential
  rw [differential]
  exact result

end LeanShared.CenteredManifoldCoordinates
