module

public import LeanShared.Dynamics.ToralCatMapAffinePatches
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Exact jets of the affine translated cat-map coordinates. The
perturbation changes only the constant term, so every positive-order
jet difference vanishes, at every finite order. -/

set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set IsManifold Bundle Function
open scoped Manifold ContDiff Bundle Topology
namespace LeanShared.ToralCatMap

theorem affineCoordinate_difference (u : Control) :
    affineCoordinate u - affineCoordinate 0 =
      fun _ => quotientCoordinateEquivalence (controlEquivalence u) := by
  funext y
  simp only [Pi.sub_apply, affineCoordinate_formula, map_zero, zero_add, add_sub_cancel_right]

theorem affineCoordinate_jet_difference (u : Control) (k : ℕ) (y : HilbertModel) :
    iteratedFDeriv ℝ k (affineCoordinate u) y - iteratedFDeriv ℝ k (affineCoordinate 0) y =
      iteratedFDeriv ℝ k (fun _ : HilbertModel => quotientCoordinateEquivalence (controlEquivalence u)) y := by
  rw [← iteratedFDeriv_sub_apply ((smooth_affineCoordinate u).of_le (by simp)).contDiffAt
    ((smooth_affineCoordinate 0).of_le (by simp)).contDiffAt, affineCoordinate_difference]

theorem affineCoordinate_jet_difference_zero (u : Control) (k : ℕ) (hk : k ≠ 0) (y : HilbertModel) :
    iteratedFDeriv ℝ k (affineCoordinate u) y - iteratedFDeriv ℝ k (affineCoordinate 0) y = 0 := by
  rw [affineCoordinate_jet_difference, iteratedFDeriv_const_of_ne hk]
  rfl

def noiseConstant : ℝ := 1 + ‖quotientCoordinateEquivalence.toContinuousLinearMap‖

theorem noiseConstant_positive : 0 < noiseConstant := by
  unfold noiseConstant
  positivity

theorem affineCoordinate_jet_difference_bound (u : Control) (k : ℕ) (y : HilbertModel) :
    ‖iteratedFDeriv ℝ k (affineCoordinate u) y - iteratedFDeriv ℝ k (affineCoordinate 0) y‖ ≤
      noiseConstant * ‖u‖ := by
  by_cases hk : k = 0
  · subst k
    rw [affineCoordinate_jet_difference, norm_iteratedFDeriv_zero]
    have control : ‖controlEquivalence u‖ ≤ ‖u‖ :=
      max_le (norm_le_pi_norm u 0) (norm_le_pi_norm u 1)
    have bound := quotientCoordinateEquivalence.toContinuousLinearMap.le_opNorm (controlEquivalence u)
    exact bound.trans ((mul_le_mul_of_nonneg_left control (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by dsimp [noiseConstant]; linarith) (norm_nonneg u)))
  · rw [affineCoordinate_jet_difference_zero u k hk, norm_zero]
    exact mul_nonneg noiseConstant_positive.le (norm_nonneg u)

end LeanShared.ToralCatMap
