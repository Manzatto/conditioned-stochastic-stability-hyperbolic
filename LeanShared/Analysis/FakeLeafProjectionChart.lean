module
public import LeanShared.Analysis.FakeLeafGraph
import all LeanShared.Analysis.FakeLeafGraph
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! The actual injective projection is a global open chart of the leaf.
Its inverse agrees with the already constructed unique inverse point. -/
public noncomputable section
open Set
namespace LeanShared.FakeLeafProjectionChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  (U : Submodule ℝ E) (Γ : Set E) [Nonempty Γ] {L : ℝ} (hL : 0 ≤ L)
  (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
    ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖)

@[expose] def inversePoint : U → Γ :=
  Function.extend (Subtype.val : FakeLeafGraph.parameterDomain U Γ → U)
    (FakeLeafGraph.point U Γ hL slope) (fun _ => Classical.choice ‹Nonempty Γ›)

theorem inversePoint_on_domain (u : FakeLeafGraph.parameterDomain U Γ) :
    inversePoint U Γ hL slope (u : U) = FakeLeafGraph.point U Γ hL slope u :=
  Subtype.val_injective.extend_apply _ _ u

theorem inverse_projection (x : Γ) :
    inversePoint U Γ hL slope (FakeLeafGraph.projection U Γ x) = x := by
  rw [inversePoint_on_domain U Γ hL slope ⟨_, x, rfl⟩]
  exact FakeLeafGraph.point_of_projection U Γ hL slope x

theorem projection_inverse (u : U) (hu : u ∈ FakeLeafGraph.parameterDomain U Γ) :
    FakeLeafGraph.projection U Γ (inversePoint U Γ hL slope u) = u := by
  rw [inversePoint_on_domain U Γ hL slope ⟨u, hu⟩]
  exact FakeLeafGraph.point_projection U Γ hL slope ⟨u, hu⟩

theorem inverse_continuousOn : ContinuousOn (inversePoint U Γ hL slope)
    (FakeLeafGraph.parameterDomain U Γ) := by
  have lip : LipschitzOnWith (Real.toNNReal (1 + L)) (inversePoint U Γ hL slope)
      (FakeLeafGraph.parameterDomain U Γ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    rw [inversePoint_on_domain U Γ hL slope ⟨u, hu⟩,
      inversePoint_on_domain U Γ hL slope ⟨v, hv⟩]
    exact (FakeLeafGraph.point_lipschitz U Γ hL slope).dist_le_mul ⟨u, hu⟩ ⟨v, hv⟩
  exact lip.continuousOn

@[expose] def chart (openDomain : IsOpen (FakeLeafGraph.parameterDomain U Γ)) :
    OpenPartialHomeomorph Γ U where
  toFun := FakeLeafGraph.projection U Γ
  invFun := inversePoint U Γ hL slope
  source := univ
  target := FakeLeafGraph.parameterDomain U Γ
  map_source' := fun x _ => ⟨x, rfl⟩
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun x _ => inverse_projection U Γ hL slope x
  right_inv' := fun u hu => projection_inverse U Γ hL slope u hu
  continuousOn_toFun := (FakeLeafGraph.projection_continuous U Γ).continuousOn
  continuousOn_invFun := inverse_continuousOn U Γ hL slope
  open_source := isOpen_univ
  open_target := openDomain
end LeanShared.FakeLeafProjectionChart
