module

public import LeanShared.Geometry.BundleEndomorphismCoordinates
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-! The kernel of a genuine bundle projection is identified with the kernel
of its actual coordinate operator by the chart's linear equivalence. -/
public noncomputable section
open Set Bundle
namespace LeanShared.BundleEndomorphismCoordinates
variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  (e : Trivialization F (Bundle.TotalSpace.proj (E := E))) [e.IsLinear ℝ]
  (P : ∀ b, E b →L[ℝ] E b)

theorem map_kernel (b : B) (inside : b ∈ e.baseSet) :
    (P b).ker.map (e.continuousLinearEquivAt ℝ b inside).toLinearMap =
      (coordinates E e P b).ker := by
  let H := e.continuousLinearEquivAt ℝ b inside
  have commute (v : E b) : coordinates E e P b (H v)=H (P b v) := by
    simp only [coordinates,ContinuousLinearMap.comp_apply,H,
      Trivialization.coe_continuousLinearEquivAt_eq,
      e.symmL_continuousLinearMapAt inside]
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩
    change coordinates E e P b (H u)=0
    rw [commute,show P b u=0 from hu,map_zero]
  · intro hv
    obtain ⟨u,rfl⟩ := H.surjective v
    refine ⟨u,?_,rfl⟩
    change P b u=0
    apply H.injective
    rw [map_zero,←commute]
    exact hv

@[expose] def kernelEquiv (b : B) (inside : b ∈ e.baseSet) :
    (P b).ker ≃L[ℝ] (coordinates E e P b).ker :=
  (e.continuousLinearEquivAt ℝ b inside).ofSubmodules _ _ (map_kernel E e P b inside)

theorem kernelEquiv_apply (b : B) (inside : b ∈ e.baseSet) (v : (P b).ker) :
    (kernelEquiv E e P b inside v).val=e.continuousLinearMapAt ℝ b v.val := by
  exact congrFun (e.coe_continuousLinearEquivAt_eq inside) v.val

end LeanShared.BundleEndomorphismCoordinates
