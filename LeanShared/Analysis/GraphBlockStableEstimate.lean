module

public import LeanShared.Analysis.GraphBlockPerturbation
public import Mathlib.Tactic.Ring

/-! The stable component of an actual perturbed block on an unstable graph. -/
public noncomputable section
namespace LeanShared.GraphBlockPerturbation
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem lower_norm_le (A : U →L[ℝ] U) (B : S →L[ℝ] S)
    (L : U × S →L[ℝ] U × S) (G : U →L[ℝ] S)
    (hG : ‖G‖ ≤ 1) (η : ℝ) (close : ‖L - A.prodMap B‖ ≤ η) :
    ‖lower L G‖ ≤ ‖B‖ * ‖G‖ + η := by
  have nonnegative : 0 ≤ η := (norm_nonneg _).trans close
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have graphBound : ‖graph G v‖ ≤ ‖v‖ := ((graph G).le_opNorm v).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (graph_norm_le G hG) (norm_nonneg v))
  have projected := norm_snd_le ((L - A.prodMap B) (graph G v))
  have error : ‖(L (v, G v)).2 - B (G v)‖ ≤ η * ‖v‖ :=
    projected.trans (((L - A.prodMap B).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right close (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left graphBound nonnegative)))
  change ‖(L (v, G v)).2‖ ≤ _
  calc
    _ ≤ ‖B (G v)‖ + ‖(L (v, G v)).2 - B (G v)‖ := norm_le_insert' _ _
    _ ≤ ‖B‖ * (‖G‖ * ‖v‖) + η * ‖v‖ := add_le_add
      ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (G.le_opNorm v) (norm_nonneg _))) error
    _ = _ := by ring

end LeanShared.GraphBlockPerturbation
