module
public import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.Linarith

/-! Connectedness of the exterior of a norm ball in real dimension at least two. -/
public section
open Set Metric
namespace LeanShared.ExteriorConnected
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isPreconnected (dimension : 1 < Module.rank ℝ E) {r : ℝ} (hr : 0 ≤ r) :
    IsPreconnected {x : E | r < ‖x‖} := by
  have domain := (isPreconnected_Ioi : IsPreconnected (Ioi r)).prod (isPreconnected_sphere dimension (0 : E) 1)
  have image := domain.image (fun p : ℝ × E => p.1 • p.2)
    (continuous_fst.smul continuous_snd).continuousOn
  have identifies : (fun p : ℝ × E => p.1 • p.2) '' (Ioi r ×ˢ sphere (0 : E) 1) =
      {x : E | r < ‖x‖} := by
    ext x
    constructor
    · rintro ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
      have normV : ‖v‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hv
      simp only [mem_ofPred_eq, norm_smul, Real.norm_eq_abs, normV, mul_one]
      rwa [abs_of_nonneg (hr.trans ht.le)]
    · intro hx
      have positive : 0 < ‖x‖ := hr.trans_lt hx
      refine ⟨(‖x‖, ‖x‖⁻¹ • x), ⟨hx, ?_⟩, ?_⟩
      · simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr positive.le), inv_mul_cancel₀ positive.ne']
      · simp only [smul_smul, mul_inv_cancel₀ positive.ne', one_smul]
  rwa [identifies] at image
end LeanShared.ExteriorConnected
