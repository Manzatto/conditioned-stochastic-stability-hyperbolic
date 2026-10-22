module
public import LeanShared.Analysis.AffineGraphJacobian
public import LeanShared.Analysis.FakeLeafGraph
import all LeanShared.Analysis.FakeLeafGraph

/-! The actual inverse projection of a full affine graph has its literal
linear height. This identifies its derived fake-leaf parametrization. -/
public noncomputable section
open Set
namespace LeanShared.AffineGraphParameter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

@[expose] def point (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (v : Uᗮ) (u : U) : E :=
  IntrinsicGraphJacobian.graphDifferential U L u+(v:E)

@[expose] def carrier (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (v : Uᗮ) : Set E :=
  range (point U L v)

theorem projection_point (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (v : Uᗮ) (u : U) :
    U.orthogonalProjectionOnto (point U L v u)=u := by
  rw [point,map_add,IntrinsicGraphJacobian.projection_graphDifferential,
    (U.orthogonalProjectionOnto_eq_zero_iff).mpr v.property,add_zero]

theorem parameterDomain (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (v : Uᗮ) :
    FakeLeafGraph.parameterDomain U (carrier U L v)=univ := by
  apply eq_univ_of_forall
  intro u
  exact ⟨⟨point U L v u,⟨u,rfl⟩⟩,projection_point U L v u⟩

theorem heightExtension (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (v : Uᗮ)
    {R : ℝ} (hR : 0 ≤ R)
    (slope : ∀ x ∈ carrier U L v, ∀ y ∈ carrier U L v,
      ‖Uᗮ.starProjection (x-y)‖ ≤ R*‖U.starProjection (x-y)‖) :
    FakeLeafGraph.heightExtension U (carrier U L v) hR slope = fun u => L u+v := by
  funext u
  have member : u ∈ FakeLeafGraph.parameterDomain U (carrier U L v) := by
    rw [parameterDomain]; trivial
  rw [FakeLeafGraph.heightExtension_on_domain U (carrier U L v) hR slope ⟨u,member⟩]
  let x : carrier U L v := ⟨point U L v u,⟨u,rfl⟩⟩
  have actual : FakeLeafGraph.point U (carrier U L v) hR slope ⟨u,member⟩=x := by
    apply FakeLeafGraph.projection_injective U (carrier U L v) hR slope
    rw [FakeLeafGraph.point_projection]
    exact (projection_point U L v u).symm
  change Uᗮ.orthogonalProjectionOnto
    (FakeLeafGraph.point U (carrier U L v) hR slope ⟨u,member⟩:E)=L u+v
  rw [actual]
  change Uᗮ.orthogonalProjectionOnto ((u:E)+(L u:E)+(v:E))=L u+v
  rw [map_add,map_add,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have zero : Uᗮ.orthogonalProjectionOnto (u:E)=0 :=
    (Uᗮ.orthogonalProjectionOnto_eq_zero_iff).mpr (by rw [Submodule.orthogonal_orthogonal]; exact u.property)
  rw [zero,zero_add]
end LeanShared.AffineGraphParameter
