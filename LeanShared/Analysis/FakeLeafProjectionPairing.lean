module
public import LeanShared.Analysis.FakeLeafProjectionChart
import all LeanShared.Analysis.FakeLeafGraph

/-! The inverse projection and literal ambient graph agree on the domain. -/
public section
open Set
namespace LeanShared.FakeLeafProjectionChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem ambient_inverse_eq_graph (U : Submodule ℝ E) (Γ : Set E) [Nonempty Γ]
    {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖)
    (u : U) (hu : u ∈ FakeLeafGraph.parameterDomain U Γ) :
    (inversePoint U Γ hL slope u : E) =
      ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hL slope) u := by
  rw [inversePoint_on_domain U Γ hL slope ⟨u, hu⟩]
  change _ = (u : E) + (FakeLeafGraph.heightExtension U Γ hL slope u : E)
  rw [FakeLeafGraph.heightExtension_on_domain U Γ hL slope ⟨u, hu⟩]
  exact FakeLeafGraph.point_eq_graph U Γ hL slope ⟨u, hu⟩
end LeanShared.FakeLeafProjectionChart
