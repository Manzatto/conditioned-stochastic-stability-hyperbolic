module
public import LeanShared.Geometry.AffineGraphGeometry
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A transverse subspace is the graph of an actual continuous linear map.
The graph is constructed by inverting the actual orthogonal projection. -/
public noncomputable section
open Set
namespace LeanShared.ProjectionComplementGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_graph (U W : Submodule ℝ E)
    (dimension : Module.finrank ℝ W=Module.finrank ℝ U)
    (injective : Function.Injective (U.orthogonalProjectionOnto.comp W.subtypeL)) :
    ∃ L : U →L[ℝ] Uᗮ, ∀ v : Uᗮ,
      AffineGraphParameter.carrier U L v=((fun w : W => (w:E)+(v:E)) '' univ) := by
  let A := U.orthogonalProjectionOnto.comp W.subtypeL
  let e : W ≃L[ℝ] U :=
    (A.toLinearMap.linearEquivOfInjective injective dimension).toContinuousLinearEquiv
  let L := Uᗮ.orthogonalProjectionOnto.comp (W.subtypeL.comp e.symm.toContinuousLinearMap)
  have eu (u : U) : U.orthogonalProjectionOnto (e.symm u:E)=u := by
    exact e.apply_symm_apply u
  have graph (u : U) : IntrinsicGraphJacobian.graphDifferential U L u=(e.symm u:E) := by
    change (u:E)+(Uᗮ.orthogonalProjectionOnto (e.symm u:E):E)=(e.symm u:E)
    have projection : U.starProjection (e.symm u:E)=(u:E) := congrArg Subtype.val (eu u)
    rw [← projection]
    exact U.starProjection_add_starProjection_orthogonal _
  refine ⟨L,fun v => ?_⟩
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    refine ⟨e.symm u,mem_univ _,?_⟩
    change (e.symm u:E)+(v:E)=IntrinsicGraphJacobian.graphDifferential U L u+(v:E)
    rw [graph]
  · rintro ⟨w,_,rfl⟩
    refine ⟨e w,?_⟩
    change IntrinsicGraphJacobian.graphDifferential U L (e w)+(v:E)=(w:E)+(v:E)
    rw [graph,e.symm_apply_apply]
end LeanShared.ProjectionComplementGraph
