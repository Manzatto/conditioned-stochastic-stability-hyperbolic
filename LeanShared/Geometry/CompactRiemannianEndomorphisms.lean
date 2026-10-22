module
public import LeanShared.Geometry.CompactRiemannianTrivializations
public import LeanShared.Geometry.BundleEndomorphismCoordinates
public import LeanShared.Topology.CompactLocalBound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Actual continuous finite-dimensional bundle endomorphisms have uniformly
bounded Riemannian operator norms on compact base sets. -/
public noncomputable section
open Set Filter Bundle
open scoped Topology
namespace LeanShared.CompactRiemannianEndomorphisms
variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

theorem exists_norm_bound (K : Set B) (compact : IsCompact K)
    (P : ∀ b, E b →L[ℝ] E b)
    (continuous : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ K}) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ‖P x‖ ≤ C := by
  apply CompactLocalBound.exists_bound compact (fun x => ‖P x‖)
  intro x hx
  let e := trivializationAt F E x
  let A := BundleEndomorphismCoordinates.coordinates E e P
  have hxBase : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have ca := BundleEndomorphismCoordinates.continuousOn_coordinates E e P K continuous
  have atPoint := (ca x ⟨hx,hxBase⟩).norm
  have at' : ContinuousWithinAt (fun y => ‖A y‖) K x := by
    rw [ContinuousWithinAt] at atPoint ⊢
    rwa [nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (e.open_baseSet.mem_nhds hxBase))] at atPoint
  obtain ⟨C,hC,frames⟩ := CompactRiemannianTrivializations.local_bound (F := F) E x
  have matrices := at'.eventually (gt_mem_nhds (lt_add_one ‖A x‖))
  let L := C*((‖A x‖+1)*C)+1
  refine ⟨L,by dsimp only [L]; positivity,?_⟩
  filter_upwards [frames.filter_mono nhdsWithin_le_nhds,matrices] with y hy hm
  have reconstruct : P y=(e.symmL ℝ y).comp ((A y).comp (e.continuousLinearMapAt ℝ y)) := by
    ext v
    simp only [A,BundleEndomorphismCoordinates.coordinates,ContinuousLinearMap.comp_apply,
      e.symmL_continuousLinearMapAt hy.1]
  have normBound : ‖P y‖ ≤ ‖e.symmL ℝ y‖*(‖A y‖*‖e.continuousLinearMapAt ℝ y‖) := by
    rw [reconstruct]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
  calc
    ‖P y‖ ≤ C*((‖A x‖+1)*C) := by
      apply normBound.trans
      apply mul_le_mul hy.2.2 _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hC.le
      exact mul_le_mul hm.le hy.2.1 (norm_nonneg _) (by positivity)
    _ ≤ L := le_add_of_nonneg_right zero_le_one
end LeanShared.CompactRiemannianEndomorphisms
