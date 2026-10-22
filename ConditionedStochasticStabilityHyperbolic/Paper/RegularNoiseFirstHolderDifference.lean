module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseDerivativeBounds
public import LeanShared.Analysis.FirstDerivativeTensorNorm
import Mathlib.Tactic

/-! The actual fractional Whitney hypothesis controls the literal
Frechet-derivative difference uniformly, retaining r−1 for 1<r<2. -/
public noncomputable section
open Set
open scoped NNReal Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]

omit [FiniteDimensional ℝ E] in
theorem Maps.first_holder_difference {T:M≃ₜM} {r:ℝ} (F:Maps (E:=E) (ι:=ι) T r)
    (hr:1<r) (hr2:r<2) (ε:NNReal) (hp:0<ε) (hw:ε≤F.window)
    (control:cube (ι:=ι) ε) (i:Fin F.atlas.count)
    (x:E) (hx:x∈F.atlas.coordinatePatch i) (y:E) (hy:y∈F.atlas.coordinatePatch i) :
    ‖(fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) x-
        fderiv ℝ (F.atlas.coordinate T i) x)-
      (fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) y-
        fderiv ℝ (F.atlas.coordinate T i) y)‖≤
      (F.constant*(ε:ℝ))*‖x-y‖^(r-1) :=by
  have floor:⌊r⌋₊=1:=(Nat.floor_eq_iff (by linarith)).mpr (by norm_num;exact ⟨hr.le,hr2⟩)
  have unequal:r≠(⌊r⌋₊:ℝ):=by rw [floor,Nat.cast_one];exact ne_of_gt hr
  have bound:=(F.whitney_bound ε hp hw control).holder unequal i x hx y hy
  rw [floor,LeanShared.FirstDerivativeTensorNorm.four_increment] at bound
  have controlBound:F.constant*‖control.val‖≤F.constant*(ε:ℝ):=
    mul_le_mul_of_nonneg_left (LeanShared.NoiseCubeRescaling.cube_norm_le (ε:ℝ) ε.property control)
      F.constant_positive.le
  simp only [Nat.cast_one] at bound
  exact bound.trans
    (mul_le_mul_of_nonneg_right controlBound (Real.rpow_nonneg (norm_nonneg _) _))
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
