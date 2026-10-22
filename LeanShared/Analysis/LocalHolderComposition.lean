module
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Quantitative local Hölder transport through an actual C¹ coordinate
map. The neighborhood and its Lipschitz constant are produced from the
derivative, permitting finite-chart transport without assumptions about
an arbitrary global metric. -/
public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.LocalHolderComposition
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]

theorem exists_bound {f : F → G} {g : E → F} {x : E} {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hg : ContDiffAt ℝ 1 g x)
    {D : Set F} (hD : D ∈ 𝓝 (g x))
    (holder : ∀ y ∈ D, ∀ z ∈ D, ‖f y - f z‖ ≤ C * ‖y - z‖ ^ a) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ g '' W ⊆ D ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ y ∈ W, ∀ z ∈ W, ‖f (g y) - f (g z)‖ ≤ A * ‖y - z‖ ^ a := by
  obtain ⟨K, L, hL, lip⟩ := hg.exists_lipschitzOnWith
  have near : g ⁻¹' D ∩ L ∈ 𝓝 x := inter_mem (hg.continuousAt.preimage_mem_nhds hD) hL
  obtain ⟨W, sub, openW, hx⟩ := mem_nhds_iff.mp near
  refine ⟨W, openW, hx, ?_, C * (K : ℝ) ^ a, by positivity, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (sub hy).1
  · intro y hy z hz
    calc
      _ ≤ C * ‖g y - g z‖ ^ a := holder _ (sub hy).1 _ (sub hz).1
      _ ≤ C * ((K : ℝ) * ‖y - z‖) ^ a :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _)
            (by simpa only [dist_eq_norm] using lip.dist_le_mul y (sub hy).2 z (sub hz).2) ha) hC
      _ = _ := by rw [Real.mul_rpow K.coe_nonneg (norm_nonneg _)]; ring
end LeanShared.LocalHolderComposition
