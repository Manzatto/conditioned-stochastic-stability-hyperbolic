module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Complementary isometric stable/unstable frames have uniform forward
bounds, and their inverse bound follows from the actual splitting projection. -/
public section
namespace LeanShared.IsometricSplitFrameBounds
variable {H P Q : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem bounds (u s : Submodule ℝ H) (projection : H →L[ℝ] H)
    (range : projection.range=s) (kernel : projection.ker=u)
    (idempotent : projection.comp projection=projection)
    (eu : P ≃ₗᵢ[ℝ] u) (es : Q ≃ₗᵢ[ℝ] s) (e : (P×Q) ≃L[ℝ] H)
    (formula : ∀ z, e z=(eu z.1:H)+(es z.2:H)) :
    ‖e.toContinuousLinearMap‖ ≤ 2 ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ 1+‖projection‖ := by
  have fix (v : s) : projection v=(v:H) := by
    have mem : (v:H) ∈ projection.range := by rw [range]; exact v.property
    obtain ⟨w,hw⟩ := mem
    rw [← hw]
    exact congrArg (fun f : H →L[ℝ] H => f w) idempotent
  have zero (v : u) : projection v=0 := by
    apply LinearMap.mem_ker.mp
    rw [kernel]
    exact v.property
  have action (z : P×Q) : projection (e z)=(es z.2:H) := by
    rw [formula,map_add,zero,fix,zero_add]
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    change ‖e z‖ ≤ 2*‖z‖
    rw [formula]
    have hu : ‖(eu z.1:H)‖=‖z.1‖ := eu.norm_map z.1
    have hs : ‖(es z.2:H)‖=‖z.2‖ := es.norm_map z.2
    have first := norm_fst_le z
    have second := norm_snd_le z
    exact (norm_add_le _ _).trans (by rw [hu,hs]; linarith)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change ‖e.symm v‖ ≤ (1+‖projection‖)*‖v‖
    have stable : (es (e.symm v).2:H)=projection v := by
      simpa only [e.apply_symm_apply] using (action (e.symm v)).symm
    have unstable : (eu (e.symm v).1:H)=v-projection v := by
      apply eq_sub_iff_add_eq.mpr
      rw [← stable,← formula,e.apply_symm_apply]
    rw [Prod.norm_def]
    apply max_le
    · have same : ‖(e.symm v).1‖=‖v-projection v‖ := by
        rw [← unstable]
        exact (eu.norm_map _).symm
      rw [same]
      calc
        _ ≤ ‖v‖+‖projection v‖ := norm_sub_le _ _
        _ ≤ ‖v‖+‖projection‖*‖v‖ := add_le_add (le_refl _) (projection.le_opNorm v)
        _ = (1+‖projection‖)*‖v‖ := by ring
    · have same : ‖(e.symm v).2‖=‖projection v‖ := by
        rw [← stable]
        exact (es.norm_map _).symm
      rw [same]
      exact (projection.le_opNorm v).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left zero_le_one) (norm_nonneg _))
end LeanShared.IsometricSplitFrameBounds
