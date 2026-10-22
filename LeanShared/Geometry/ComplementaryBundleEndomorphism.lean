module
public import Mathlib.Topology.VectorBundle.Basic

/-! Subtracting a continuous fiber endomorphism from the identity is
continuous on the genuine total space, without a global trivialization. -/
public noncomputable section
namespace LeanShared.ComplementaryBundleEndomorphism
open Set Bundle Filter
open scoped Topology

theorem continuousOn
    {𝕜 B F : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace 𝕜 (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (P : ∀ b, E b →L[𝕜] E b) (K : Set B)
    (continuous : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj, P v.proj v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ K}) :
    ContinuousOn (fun v : TotalSpace F E => (⟨v.proj, v.2 - P v.proj v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ K} := by
  intro v hv
  let e := trivializationAt F E v.proj
  have base : v.proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F E v.proj
  have cp := (FiberBundle.continuousWithinAt_totalSpace F _).mp (continuous v hv)
  have ci := (FiberBundle.continuousWithinAt_totalSpace F (id : TotalSpace F E → TotalSpace F E)
    (s := {w | w.proj ∈ K}) (x₀ := v)).mp
    continuousWithinAt_id
  apply (FiberBundle.continuousWithinAt_totalSpace F _).mpr
  refine ⟨ci.1,?_⟩
  have coded := ci.2.sub cp.2
  apply coded.congr_of_eventuallyEq
  have eventual : ∀ᶠ w : TotalSpace F E in 𝓝[{w | w.proj ∈ K}] v, w.proj ∈ e.baseSet :=
    ci.1.eventually (e.open_baseSet.mem_nhds base)
  filter_upwards [eventual] with w hw
  change (e (⟨w.proj,w.2 - P w.proj w.2⟩ : TotalSpace F E)).2 =
    (e w).2 - (e (⟨w.proj,P w.proj w.2⟩ : TotalSpace F E)).2
  simpa only [Trivialization.linearMapAt_apply, ite_eq_left hw] using
    (e.linearMapAt 𝕜 w.proj).map_sub w.2 (P w.proj w.2)

  change (e (⟨v.proj,v.2 - P v.proj v.2⟩ : TotalSpace F E)).2 =
    (e v).2 - (e (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E)).2
  simpa only [Trivialization.linearMapAt_apply, ite_eq_left base] using
    (e.linearMapAt 𝕜 v.proj).map_sub v.2 (P v.proj v.2)

end LeanShared.ComplementaryBundleEndomorphism
