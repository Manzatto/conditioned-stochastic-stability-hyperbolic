module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import LeanShared.Analysis.FirstDerivativeDifferenceNorm

/-! The literal fractional Whitney certificate supplies actual first-derivative
operator bounds for the map family. This is a direct ordinary-source bridge
for nonlinear hyperbolic chart constructions; no graph/manifold theorem or
completed transfer bound is assumed. -/
public section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped NNReal

 theorem WhitneyAtlas.Bound.fderiv_close
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] {T : M → M}
    {A : WhitneyAtlas (E := E) T} {r : ℝ} {f : M → M} {δ : ℝ}
    (b : A.Bound r f δ) (regularity : 1 ≤ r)
    (i : Fin A.count) (y : E) (inside : y ∈ A.coordinatePatch i) :
    ‖fderiv ℝ (A.coordinate f i) y - fderiv ℝ (A.coordinate T i) y‖ ≤ δ := by
  rw [LeanShared.FirstDerivativeDifferenceNorm.norm_sub_eq]
  exact b.derivatives i 1 ((Nat.one_le_floor_iff r).mpr regularity) y inside

theorem Maps.coordinate_fderiv_close
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window)
    (control : cube (ι := ι) ε) (i : Fin F.atlas.count) (y : E)
    (inside : y ∈ F.atlas.coordinatePatch i) :
    ‖fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) y -
      fderiv ℝ (F.atlas.coordinate T i) y‖ ≤ F.constant * (ε : ℝ) :=
  ((F.whitney_bound ε positive window control).fderiv_close regularity i y inside).trans
    (mul_le_mul_of_nonneg_left (LeanShared.NoiseCubeRescaling.cube_norm_le
      (ε : ℝ) ε.property control) F.constant_positive.le)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
