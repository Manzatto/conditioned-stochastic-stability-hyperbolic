module
public import LeanShared.Analysis.LocalHolderBilinear

/-! Quantitative Holder estimates under a fixed bounded bilinear map. -/
public noncomputable section
namespace LeanShared.UniformBilinearHolder
variable {E F G H:Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem bound (L:F→L[ℝ]G→L[ℝ]H) {N:ℝ} (hN:0≤N)
    (normL:∀u v,‖L u v‖≤N*‖u‖*‖v‖) {f:E→F} {g:E→G}
    {K:Set E} {a B C D Q:ℝ} (hB:0≤B) (hC:0≤C) (_hD:0≤D) (_hQ:0≤Q)
    (vf:∀x∈K,‖f x‖≤B) (vg:∀x∈K,‖g x‖≤Q)
    (hf:∀x∈K,∀y∈K,‖f x-f y‖≤C*‖x-y‖^a)
    (hg:∀x∈K,∀y∈K,‖g x-g y‖≤D*‖x-y‖^a) :
    ∀x∈K,∀y∈K,‖L (f x) (g x)-L (f y) (g y)‖≤
      N*(B*D+C*Q)*‖x-y‖^a := by
  intro x hx y hy
  have split : L (f x) (g x)-L (f y) (g y)=
      L (f x) (g x-g y)+L (f x-f y) (g y) := by
    simp only [map_sub,sub_apply]; abel
  rw [split]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ N*‖f x‖*‖g x-g y‖+N*‖f x-f y‖*‖g y‖ :=
      add_le_add (normL _ _)
        (normL _ _)
    _ ≤ N*B*(D*‖x-y‖^a)+N*(C*‖x-y‖^a)*Q := by
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left (vf x hx) hN)
          (hg x hx y hy) (norm_nonneg _) (by positivity))
        (mul_le_mul (mul_le_mul_of_nonneg_left (hf x hx y hy) hN)
          (vg y hy) (norm_nonneg _) (by positivity))
    _ = _ := by ring
end LeanShared.UniformBilinearHolder
