module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseFirstHolderDifference
public import LeanShared.Geometry.FractionalChartHolderCompact
import Mathlib.Tactic

/-! Uniform actual first-derivative Holder controls in the literal Whitney
patches, from the manuscript's C^r distance and actual deterministic
regularity. No reference chart seminorm or scale continuity is input. -/
public noncomputable section
open Set IsManifold
open scoped NNReal Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]

omit [FiniteDimensional ℝ E] in
theorem Maps.uniform_whitney_first_holder_bounds {T:M≃ₜM} {r:ℝ}
    (F:Maps (E:=E) (ι:=ι) T r) (hr:1<r) (hr2:r<2)
    (regular:LeanShared.FractionalManifoldRegularity.Regular (E:=E) (F:=E) r T)
    (i:Fin F.atlas.count) {K:Set E} (compact:IsCompact K) (inside:K⊆F.atlas.coordinatePatch i) :
    ∃B C:ℝ,0≤B ∧ 0≤C ∧∀ε:NNReal,0<ε→ε≤F.window→∀control:cube (ι:=ι) ε,
      (∀x∈K,‖fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) x‖≤B) ∧
      ∀x∈K,∀y∈K,
        ‖fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) x-
          fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) y‖≤C*‖x-y‖^(r-1) :=by
  have ha:0<r-1:=by linarith
  have ha1:r-1<1:=by linarith
  have shifted:LeanShared.FractionalManifoldRegularity.Regular (E:=E) (F:=E) ((r-1)+1) T:=by
    simpa only [sub_add_cancel] using regular
  have valid:∀x∈K,x∈(F.atlas.source i).target ∧ T ((F.atlas.source i).symm x)∈(F.atlas.target i).source:=by
    intro x hx
    exact ⟨(inside hx).1,F.atlas.deterministic_target i ⟨_,subset_closure (inside hx).2,rfl⟩⟩
  obtain ⟨B,C,hB,hC,referenceValue,referenceHolder⟩:=shifted.compact_one_holder_in_charts ha ha1
    (F.atlas.source i) (F.atlas.target i) (F.atlas.source_smooth i) (F.atlas.target_smooth i) compact valid
  let D:=F.constant*(F.window:ℝ)
  have hD:0≤D:=mul_nonneg F.constant_positive.le F.window.property
  refine ⟨B+D,C+D,add_nonneg hB hD,add_nonneg hC hD,?_⟩
  intro ε hp hw control
  have floor:⌊r⌋₊=1:=(Nat.floor_eq_iff (by linarith)).mpr (by norm_num;exact ⟨hr.le,hr2⟩)
  have proximity:F.constant*‖control.val‖≤D:=
    (mul_le_mul_of_nonneg_left (LeanShared.NoiseCubeRescaling.cube_norm_le (ε:ℝ) ε.property control)
      F.constant_positive.le).trans (mul_le_mul_of_nonneg_left (show (ε:ℝ)≤(F.window:ℝ) by exact_mod_cast hw)
        F.constant_positive.le)
  constructor
  · intro x hx
    have difference:=(F.whitney_bound ε hp hw control).derivatives i 1 (by rw [floor]) x (inside hx)
    rw [←LeanShared.FirstDerivativeTensorNorm.tensor_fderiv _ x,
      ←LeanShared.FirstDerivativeTensorNorm.tensor_fderiv _ x,←map_sub,LinearIsometryEquiv.norm_map] at difference
    have reference:‖fderiv ℝ (F.atlas.coordinate T i) x‖≤B:=referenceValue x hx
    exact (norm_le_norm_sub_add _ _).trans
      ((add_le_add (difference.trans proximity) reference).trans_eq (by ring))
  · intro x hx y hy
    have difference:=F.first_holder_difference hr hr2 ε hp hw control i x (inside hx) y (inside hy)
    have reference:‖fderiv ℝ (F.atlas.coordinate T i) x-fderiv ℝ (F.atlas.coordinate T i) y‖≤C*‖x-y‖^(r-1):=
      referenceHolder x hx y hy
    have split:fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) x-
        fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) y=
      ((fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) x-fderiv ℝ (F.atlas.coordinate T i) x)-
        (fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) y-fderiv ℝ (F.atlas.coordinate T i) y))+
          (fderiv ℝ (F.atlas.coordinate T i) x-fderiv ℝ (F.atlas.coordinate T i) y):=by abel
    rw [split]
    have scale:F.constant*(ε:ℝ)≤D:=mul_le_mul_of_nonneg_left
      (show (ε:ℝ)≤(F.window:ℝ) by exact_mod_cast hw) F.constant_positive.le
    calc
      _ ≤ _:=norm_add_le _ _
      _ ≤ (F.constant*(ε:ℝ))*‖x-y‖^(r-1)+C*‖x-y‖^(r-1):=add_le_add difference reference
      _ ≤ D*‖x-y‖^(r-1)+C*‖x-y‖^(r-1):=
        add_le_add (mul_le_mul_of_nonneg_right scale (Real.rpow_nonneg (norm_nonneg _) _)) le_rfl
      _ = _:=by ring
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
