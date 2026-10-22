module
public import LeanShared.Geometry.AffineImmersionChart
public import LeanShared.Geometry.EmbeddedSubmanifoldVolume
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Every affine subspace of the actual model dimension is an embedded C¹
submanifold, with a chart constructed from a continuous linear equivalence. -/
public noncomputable section
open Set
namespace LeanShared.AffineSubspaceEmbedded
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem embedded (U P : Submodule ℝ E) (e : U ≃L[ℝ] P) (a : E) :
    EmbeddedSubmanifoldVolume.Embedded U ((fun v : P => (v:E)+a) '' univ) := by
  let i := P.subtypeL.comp e.toContinuousLinearMap
  let r := e.symm.toContinuousLinearMap.comp P.orthogonalProjectionOnto
  have left (u : U) : r (i u)=u := by
    simp only [r,i,ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
  have same : AffineImmersionChart.carrier i a = ((fun v : P => (v:E)+a) '' univ) := by
    ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨e u,mem_univ _,rfl⟩
    · rintro ⟨v,_,rfl⟩
      refine ⟨e.symm v,?_⟩
      simp only [i,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply,Submodule.subtypeL_apply]
  rw [← same]
  exact AffineImmersionChart.exists_chart i r left a
end LeanShared.AffineSubspaceEmbedded
