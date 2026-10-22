module
public import Mathlib.Topology.VectorBundle.Riemannian
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A finite-dimensional evaluation criterion for continuous bilinear bundle
sections. Useful for pullback metrics and finite adapted inner products. -/
public noncomputable section
open Set Bundle ContinuousLinearMap
namespace LeanShared.BilinearBundleContinuity
variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

theorem of_pairings (g : ∀ x, E x →L[ℝ] E x →L[ℝ] ℝ)
    (pairings : ∀ U : Set B, ∀ v w : ∀ x, E x,
      ContinuousOn (fun x => (⟨x, v x⟩ : TotalSpace F E)) U →
      ContinuousOn (fun x => (⟨x, w x⟩ : TotalSpace F E)) U →
      ContinuousOn (fun x => g x (v x) (w x)) U) :
    Continuous (fun x => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun y => E y →L[ℝ] E y →L[ℝ] ℝ) x (g x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_section]
  let e := trivializationAt F E x
  let U := e.baseSet
  have hx : x ∈ U := FiberBundle.mem_baseSet_trivializationAt' x
  have openU : IsOpen U := e.open_baseSet
  have coords : ContinuousOn
      (fun y => inCoordinates F E (F →L[ℝ] ℝ)
        (fun z => E z →L[ℝ] ℝ) x y x y (g y)) U := by
    apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    intro w
    have localInput (a : F) : ContinuousOn
        (fun y => (⟨y, e.symm y a⟩ : TotalSpace F E)) U :=
      e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy => ⟨hy, mem_univ a⟩)
    have h := pairings U (fun y => e.symm y v) (fun y => e.symm y w)
      (localInput v) (localInput w)
    apply h.congr
    intro y hy
    dsimp only
    rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := Bundle.Trivial B ℝ) hy hy (by simp)]
    simp [e]
  have atPoint := coords.continuousAt (openU.mem_nhds hx)
  simpa only [hom_trivializationAt_apply] using atPoint

/-- Relative version, so an invariant splitting only continuous on a compact
core need not be extended to the ambient manifold. -/
theorem of_pairingsOn (K : Set B) (g : ∀ x, E x →L[ℝ] E x →L[ℝ] ℝ)
    (pairings : ∀ U : Set B, U ⊆ K → ∀ v w : ∀ x, E x,
      ContinuousOn (fun x => (⟨x, v x⟩ : TotalSpace F E)) U →
      ContinuousOn (fun x => (⟨x, w x⟩ : TotalSpace F E)) U →
      ContinuousOn (fun x => g x (v x) (w x)) U) :
    ContinuousOn (fun x => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun y => E y →L[ℝ] E y →L[ℝ] ℝ) x (g x)) K := by
  intro x hx
  rw [FiberBundle.continuousWithinAt_section]
  let e := trivializationAt F E x
  let U := K ∩ e.baseSet
  have coords : ContinuousOn
      (fun y => inCoordinates F E (F →L[ℝ] ℝ)
        (fun z => E z →L[ℝ] ℝ) x y x y (g y)) U := by
    apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    intro w
    have localInput (a : F) : ContinuousOn
        (fun y => (⟨y, e.symm y a⟩ : TotalSpace F E)) U :=
      (e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy => ⟨hy, mem_univ a⟩)).mono inter_subset_right
    apply (pairings U inter_subset_left (fun y => e.symm y v) (fun y => e.symm y w)
      (localInput v) (localInput w)).congr
    intro y hy
    dsimp only
    rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := Bundle.Trivial B ℝ)
      hy.2 hy.2 (by simp)]
    simp [e]
  have atPoint := coords x ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have outside : ContinuousWithinAt
      (fun y => inCoordinates F E (F →L[ℝ] ℝ)
        (fun z => E z →L[ℝ] ℝ) x y x y (g y)) K x := by
    rw [ContinuousWithinAt] at atPoint ⊢
    rwa [nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)))] at atPoint
  simpa only [hom_trivializationAt_apply] using outside

omit [FiniteDimensional ℝ F] in
/-- Fiberwise subtraction preserves continuous total-space sections. -/
theorem sub_sections {X : Type*} [TopologicalSpace X] (K : Set X) (b : X → B)
    (v w : ∀ x, E (b x))
    (cv : ContinuousOn (fun x => (⟨b x, v x⟩ : TotalSpace F E)) K)
    (cw : ContinuousOn (fun x => (⟨b x, w x⟩ : TotalSpace F E)) K) :
    ContinuousOn (fun x => (⟨b x, v x - w x⟩ : TotalSpace F E)) K := by
  intro x hx
  have hv := cv x hx
  have hw := cw x hx
  rw [FiberBundle.continuousWithinAt_totalSpace] at hv hw ⊢
  refine ⟨hv.1, ?_⟩
  refine (hv.2.sub hw.2).congr_of_eventuallyEq_of_mem ?_ hx
  let e := trivializationAt F E (b x)
  have eventuallyBase := hv.1.eventually (e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' (b x)))
  filter_upwards [eventuallyBase] with y hy
  change (e ⟨b y, v y - w y⟩).2 = (e ⟨b y, v y⟩).2 - (e ⟨b y, w y⟩).2
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hy,
    ← Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hy,
    ← Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hy, map_sub]

end LeanShared.BilinearBundleContinuity
