module
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! An actual continuous endomorphism of a finite-dimensional vector bundle
has continuous operator-valued matrices in every genuine local trivialization.
This derives coordinate projection continuity from the total-space splitting
continuity in HyperbolicData, rather than assuming unrelated continuous matrix
fields. -/
public noncomputable section
namespace LeanShared.BundleEndomorphismCoordinates
open Set Bundle

@[expose] def coordinates {𝕜 B F : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace 𝕜 (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (e : Trivialization F (Bundle.TotalSpace.proj (E := E))) [e.IsLinear 𝕜]
    (P : ∀ b, E b →L[𝕜] E b) (b : B) : F →L[𝕜] F :=
  (e.continuousLinearMapAt 𝕜 b).comp ((P b).comp (e.symmL 𝕜 b))

theorem continuousOn_coordinates {𝕜 B F : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [TopologicalSpace B]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace 𝕜 (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (e : Trivialization F (Bundle.TotalSpace.proj (E := E))) [e.IsLinear 𝕜]
    (P : ∀ b, E b →L[𝕜] E b) (K : Set B)
    (continuous : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj, P v.proj v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ K}) :
    ContinuousOn (coordinates E e P) (K ∩ e.baseSet) := by
  apply continuousOn_clm_apply.mpr
  intro v
  have inputSection : ContinuousOn (fun b => (⟨b, e.symm b v⟩ : TotalSpace F E)) e.baseSet :=
    e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun b hb => ⟨hb, mem_univ v⟩)
  have projected : ContinuousOn (fun b => (⟨b, P b (e.symm b v)⟩ : TotalSpace F E))
      (K ∩ e.baseSet) :=
    continuous.comp (inputSection.mono inter_subset_right) (fun _ hb => hb.1)
  have coded := e.continuousOn.comp projected (fun b hb => e.mem_source.mpr hb.2)
  apply coded.snd.congr
  intro b hb
  simp only [coordinates, ContinuousLinearMap.comp_apply,
    e.symmL_apply hb.2, Function.comp_def, Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e hb.2]

theorem coordinates_idempotent {𝕜 B F : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace 𝕜 (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (e : Trivialization F (Bundle.TotalSpace.proj (E := E))) [e.IsLinear 𝕜]
    (P : ∀ b, E b →L[𝕜] E b) (b : B) (inside : b ∈ e.baseSet)
    (idempotent : ∀ x, P b (P b x) = P b x) (v : F) :
    coordinates E e P b (coordinates E e P b v) = coordinates E e P b v := by
  simp only [coordinates, ContinuousLinearMap.comp_apply,
    e.symmL_continuousLinearMapAt inside, idempotent]

end LeanShared.BundleEndomorphismCoordinates
