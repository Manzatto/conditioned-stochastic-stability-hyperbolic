module
public import LeanShared.Geometry.BundleEndomorphismCoordinates
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-! Exact identification of a fiber endomorphism range with the range of its
actual local coordinate matrix. This connects local projection-range frames
to the genuine stable/unstable tangent subspaces, with no assumed norm or
space-identification certificate. -/
public noncomputable section
namespace LeanShared.BundleEndomorphismCoordinates
open Set Bundle

section
variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  (e : Trivialization F (Bundle.TotalSpace.proj (E := E))) [e.IsLinear 𝕜]
  (P : ∀ b, E b →L[𝕜] E b) (b : B)

theorem range_coordinates_eq_map (inside : b ∈ e.baseSet) :
    (coordinates E e P b).range =
      (P b).range.map (e.continuousLinearMapAt 𝕜 b).toLinearMap := by
  ext y
  constructor
  · rintro ⟨v, image⟩
    change coordinates E e P b v = y at image
    refine ⟨P b (e.symmL 𝕜 b v), ⟨e.symmL 𝕜 b v, rfl⟩, ?_⟩
    exact image
  · rintro ⟨z, ⟨v, image⟩, target⟩
    change P b v = z at image
    change e.continuousLinearMapAt 𝕜 b z = y at target
    refine ⟨e.continuousLinearMapAt 𝕜 b v, ?_⟩
    change coordinates E e P b (e.continuousLinearMapAt 𝕜 b v) = y
    simp only [coordinates, ContinuousLinearMap.comp_apply,
      e.symmL_continuousLinearMapAt inside]
    rw [image, target]

@[expose] def rangeCoordinatesEquiv (inside : b ∈ e.baseSet) :
    (P b).range ≃L[𝕜] (coordinates E e P b).range :=
  (e.continuousLinearEquivAt 𝕜 b inside).ofSubmodules _ _ (by
    change (P b).range.map
      ((e.continuousLinearEquivAt 𝕜 b inside : E b →L[𝕜] F).toLinearMap) = _
    rw [e.coe_continuousLinearEquivAt_eq' inside, range_coordinates_eq_map E e P b inside])

theorem finrank_coordinates_eq (inside : b ∈ e.baseSet) :
    Module.finrank 𝕜 (coordinates E e P b).range = Module.finrank 𝕜 (P b).range :=
  (rangeCoordinatesEquiv E e P b inside).toLinearEquiv.finrank_eq.symm

end
end LeanShared.BundleEndomorphismCoordinates
