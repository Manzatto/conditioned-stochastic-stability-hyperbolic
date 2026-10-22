module
public import LeanShared.Geometry.BundleEndomorphismCoordinates

/-! Projection cocycle identities in independently chosen source and target
bundle charts. These coordinate identities follow from actual fiber maps;
neither a global trivialization nor a coherent chart-selection source is
required. -/
public noncomputable section
namespace LeanShared.BundleProjectionCocycleCoordinates
open Bundle

variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

@[expose] def map (e f : Trivialization F (TotalSpace.proj (E := E)))
    [e.IsLinear ℝ] [f.IsLinear ℝ] (x y : B) (A : E x →L[ℝ] E y) : F →L[ℝ] F :=
  (f.continuousLinearMapAt ℝ y).comp (A.comp (e.symmL ℝ x))

theorem intertwines (e f : Trivialization F (TotalSpace.proj (E := E)))
    [e.IsLinear ℝ] [f.IsLinear ℝ] (P : ∀ b, E b →L[ℝ] E b)
    (x y : B) (hx : x ∈ e.baseSet) (hy : y ∈ f.baseSet)
    (A : E x →L[ℝ] E y) (invariant : (P y).comp A = A.comp (P x)) :
    (BundleEndomorphismCoordinates.coordinates E f P y).comp (map E e f x y A) =
      (map E e f x y A).comp (BundleEndomorphismCoordinates.coordinates E e P x) := by
  ext v
  have same := congrArg (fun L : E x →L[ℝ] E y => L (e.symmL ℝ x v)) invariant
  simp only [ContinuousLinearMap.comp_apply] at same
  simp only [map, BundleEndomorphismCoordinates.coordinates, ContinuousLinearMap.comp_apply,
    f.symmL_continuousLinearMapAt hy, e.symmL_continuousLinearMapAt hx, same]

omit [VectorBundle ℝ F E] in
theorem inverse_left (e f : Trivialization F (TotalSpace.proj (E := E)))
    [e.IsLinear ℝ] [f.IsLinear ℝ] (x y : B)
    (hx : x ∈ e.baseSet) (hy : y ∈ f.baseSet) (A : E x ≃L[ℝ] E y) :
    (map E f e y x A.symm.toContinuousLinearMap).comp
      (map E e f x y A.toContinuousLinearMap) = ContinuousLinearMap.id ℝ F := by
  ext v
  simp only [map, ContinuousLinearMap.comp_apply, f.symmL_continuousLinearMapAt hy,
    ContinuousLinearEquiv.coe_coe, A.symm_apply_apply,
    e.continuousLinearMapAt_symmL hx, ContinuousLinearMap.id_apply]

end LeanShared.BundleProjectionCocycleCoordinates
