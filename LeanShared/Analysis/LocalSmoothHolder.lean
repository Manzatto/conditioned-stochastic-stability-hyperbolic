module
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Local C¹ regularity gives actual two-point fractional Hölder bounds on
an open neighborhood contained in any prescribed neighborhood. -/
public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.LocalSmoothHolder
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The neighborhood is chosen with diameter at most one, so the same
Lipschitz constant controls every exponent at most one. -/
theorem exists_holder_on {g : E → F} {x : E} (hg : ContDiffAt ℝ 1 g x)
    {a : ℝ} (ha : a ≤ 1) {D : Set E} (hD : D ∈ 𝓝 x) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ D ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ W, ∀ z ∈ W, ‖g y - g z‖ ≤ C * ‖y - z‖ ^ a := by
  obtain ⟨K, L, hL, hLip⟩ := hg.exists_lipschitzOnWith
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hD hL)
  let δ : ℝ := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_, K, K.coe_nonneg, ?_⟩
  · intro y hy
    exact (hsub ((Metric.ball_subset_ball (min_le_left ε (1 / 2))) hy)).1
  · intro y hy z hz
    have hy' := (hsub ((Metric.ball_subset_ball (min_le_left ε (1 / 2))) hy)).2
    have hz' := (hsub ((Metric.ball_subset_ball (min_le_left ε (1 / 2))) hz)).2
    have small : ‖y - z‖ ≤ 1 := by
      have hdist := dist_triangle y x z
      have hxy : dist y x < δ := hy
      have hxz : dist x z < δ := by simpa only [Metric.mem_ball, dist_comm] using hz
      rw [← dist_eq_norm]
      dsimp [δ] at hxy hxz
      linarith [min_le_right ε (1 / 2)]
    have lip : ‖g y - g z‖ ≤ (K : ℝ) * ‖y - z‖ := by
      simpa only [dist_eq_norm] using hLip.dist_le_mul y hy' z hz'
    exact lip.trans (mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_le_one (norm_nonneg _) small ha) K.coe_nonneg)
end LeanShared.LocalSmoothHolder
