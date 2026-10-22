module
public import LeanShared.Geometry.CompactRiemannianTrivializations
public import LeanShared.Topology.CompactLocalBound
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Positivity

/-! Uniform bounds for actual continuous linear bundle maps on compact bases.
The fiber metric is continuous; the maps need only be continuous on the compact set. -/
public noncomputable section
open Set Filter Bundle
open scoped Topology
namespace LeanShared.CompactRiemannianBundleMaps
variable {B F G : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

omit [FiniteDimensional ℝ G] in
theorem to_fixed (K : Set B) (compact : IsCompact K)
    (A : ∀ b, E b →L[ℝ] G)
    (continuous : ContinuousOn (fun v : TotalSpace F E => A v.proj v.2)
      {v | v.proj ∈ K}) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ‖A x‖ ≤ C := by
  apply CompactLocalBound.exists_bound compact (fun x => ‖A x‖)
  intro x hx
  let e := trivializationAt F E x
  let a := fun y => (A y).comp (e.symmL ℝ y)
  have ca : ContinuousOn a (K ∩ e.baseSet) := by
    apply continuousOn_clm_apply.mpr
    intro v
    have input : ContinuousOn (fun b => (⟨b,e.symm b v⟩ : TotalSpace F E)) e.baseSet :=
      e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun b hb => ⟨hb,mem_univ v⟩)
    apply (continuous.comp (input.mono inter_subset_right) (fun _ hb => hb.1)).congr
    intro b hb
    simp only [a,ContinuousLinearMap.comp_apply,e.symmL_apply hb.2,Function.comp_def]
  have atPoint := (ca x ⟨hx,FiberBundle.mem_baseSet_trivializationAt' x⟩).norm
  have at' : ContinuousWithinAt (fun y => ‖a y‖) K x := by
    rw [ContinuousWithinAt] at atPoint ⊢
    rwa [nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)))] at atPoint
  obtain ⟨C,hC,frames⟩ := CompactRiemannianTrivializations.local_bound (F := F) E x
  have matrices := at'.eventually (gt_mem_nhds (lt_add_one ‖a x‖))
  refine ⟨(‖a x‖+1)*C+1,by positivity,?_⟩
  filter_upwards [frames.filter_mono nhdsWithin_le_nhds,matrices] with y hy hm
  have reconstruct : A y=(a y).comp (e.continuousLinearMapAt ℝ y) := by
    ext v
    simp only [a,ContinuousLinearMap.comp_apply,e.symmL_continuousLinearMapAt hy.1]
  calc
    ‖A y‖ ≤ ‖a y‖*‖e.continuousLinearMapAt ℝ y‖ := by
      rw [reconstruct]; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖a x‖+1)*C := mul_le_mul hm.le hy.2.1 (norm_nonneg _) (by positivity)
    _ ≤ (‖a x‖+1)*C+1 := le_add_of_nonneg_right zero_le_one

omit [FiniteDimensional ℝ F] in
theorem from_fixed (K : Set B) (compact : IsCompact K)
    (A : ∀ b, G →L[ℝ] E b)
    (continuous : ∀ v : G, ContinuousOn (fun b => (⟨b,A b v⟩ : TotalSpace F E)) K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ‖A x‖ ≤ C := by
  apply CompactLocalBound.exists_bound compact (fun x => ‖A x‖)
  intro x hx
  let e := trivializationAt F E x
  let a := fun y => (e.continuousLinearMapAt ℝ y).comp (A y)
  have ca : ContinuousOn a (K ∩ e.baseSet) := by
    apply continuousOn_clm_apply.mpr
    intro v
    have coded := e.continuousOn.comp ((continuous v).mono inter_subset_left)
      (fun b hb => e.mem_source.mpr hb.2)
    apply coded.snd.congr
    intro b hb
    simp only [a,ContinuousLinearMap.comp_apply,
      Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hb.2,Function.comp_def]
  have atPoint := (ca x ⟨hx,FiberBundle.mem_baseSet_trivializationAt' x⟩).norm
  have at' : ContinuousWithinAt (fun y => ‖a y‖) K x := by
    rw [ContinuousWithinAt] at atPoint ⊢
    rwa [nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)))] at atPoint
  obtain ⟨C,hC,frames⟩ := CompactRiemannianTrivializations.local_bound (F := F) E x
  have matrices := at'.eventually (gt_mem_nhds (lt_add_one ‖a x‖))
  refine ⟨C*(‖a x‖+1)+1,by positivity,?_⟩
  filter_upwards [frames.filter_mono nhdsWithin_le_nhds,matrices] with y hy hm
  have reconstruct : A y=(e.symmL ℝ y).comp (a y) := by
    ext v
    simp only [a,ContinuousLinearMap.comp_apply,e.symmL_continuousLinearMapAt hy.1]
  calc
    ‖A y‖ ≤ ‖e.symmL ℝ y‖*‖a y‖ := by
      rw [reconstruct]; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C*(‖a x‖+1) := mul_le_mul hy.2.2 hm.le (norm_nonneg _) hC.le
    _ ≤ C*(‖a x‖+1)+1 := le_add_of_nonneg_right zero_le_one
end LeanShared.CompactRiemannianBundleMaps
