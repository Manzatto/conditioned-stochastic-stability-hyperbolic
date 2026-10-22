module

public import LeanShared.Geometry.BundleProjectionKernelEquiv
public import LeanShared.Analysis.ProjectionKernelTransport

/-! Continuous local frames for the kernels of actual continuous bundle
projections. The frames are constructed from a single genuine chart and
near-identity projection transport, without an assumed frame-continuity law. -/
public noncomputable section
open Set Bundle
namespace LeanShared.BundleKernelFrames
variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  (e : Trivialization F (Bundle.TotalSpace.proj (E := E))) [e.IsLinear ℝ]
  (P : ∀ b, E b →L[ℝ] E b) (K : Set B) (b : B) (hb : b ∈ e.baseSet)
  (inside : K ⊆ e.baseSet)
  (idem : ∀ x ∈ insert b K, ∀ v, P x (P x v)=P x v)
  (small : ∀ x ∈ K,
    ‖BundleEndomorphismCoordinates.coordinates E e P b -
      BundleEndomorphismCoordinates.coordinates E e P x‖ *
      (2*‖BundleEndomorphismCoordinates.coordinates E e P b‖+1)<1)

omit [FiniteDimensional ℝ F] in
include idem in
theorem coordinate_idem (x : B) (hchart : x ∈ e.baseSet) (hx : x ∈ insert b K) :
    ∀ v, BundleEndomorphismCoordinates.coordinates E e P x
      (BundleEndomorphismCoordinates.coordinates E e P x v)=
        BundleEndomorphismCoordinates.coordinates E e P x v :=
  BundleEndomorphismCoordinates.coordinates_idempotent E e P x hchart (idem x hx)

@[expose] def frame (x : K) : (P b).ker ≃L[ℝ] (P x.val).ker :=
  (BundleEndomorphismCoordinates.kernelEquiv E e P b hb).trans
    ((IntertwiningProjectionTransport.kernelEquivalence _ _
      (coordinate_idem E e P K b idem b hb (mem_insert b K))
      (coordinate_idem E e P K b idem x.val (inside x.property) (mem_insert_of_mem b x.property))
      (small x.val x.property)).trans
      (BundleEndomorphismCoordinates.kernelEquiv E e P x.val (inside x.property)).symm)

theorem continuous_frame (splitting : ContinuousOn
    (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E))
    {v | v.proj ∈ K}) (u : (P b).ker) :
    Continuous (fun x : K => (⟨x.val,(frame E e P K b hb inside idem small x u).val⟩ : TotalSpace F E)) := by
  let Q := BundleEndomorphismCoordinates.coordinates E e P
  have contQ : Continuous (fun x : K => Q x.val) := by
    have q : ContinuousOn Q K :=
      (BundleEndomorphismCoordinates.continuousOn_coordinates E e P K splitting).mono
        (fun x hx => ⟨hx,inside hx⟩)
    exact continuousOn_iff_continuous_domRestrict.mp q
  have contR : Continuous (fun x : K =>
      IntertwiningProjectionTransport.transport (Q b) (Q x.val)) :=
    (contQ.clm_comp_const _).add ((continuous_const.sub contQ).clm_comp_const _)
  have contV : Continuous (fun x : K =>
      IntertwiningProjectionTransport.transport (Q b) (Q x.val)
        (e.continuousLinearMapAt ℝ b u.val)) :=
    (ContinuousLinearMap.apply ℝ F (e.continuousLinearMapAt ℝ b u.val)).continuous.comp contR
  have actual := e.continuousOn_symm.comp
    (continuous_subtype_val.prodMk contV).continuousOn (s := univ)
    (fun x _ => ⟨inside x.property,mem_univ _⟩)
  apply (continuousOn_univ.mp actual).congr
  intro x
  simp only [frame,ContinuousLinearEquiv.trans_apply,BundleEndomorphismCoordinates.kernelEquiv,
    IntertwiningProjectionTransport.kernelEquivalence,ContinuousLinearEquiv.ofSubmodules_apply,
    ContinuousLinearEquiv.ofSubmodules_symm_apply,
    IntertwiningProjectionTransport.equivalence_apply,
    Trivialization.coe_continuousLinearEquivAt_eq,
    Trivialization.symm_continuousLinearEquivAt_eq]
  exact congrArg (fun v : E x.val => (⟨x.val,v⟩ : TotalSpace F E))
    (e.symmL_apply (R := ℝ) (inside x.property) _).symm

end LeanShared.BundleKernelFrames
