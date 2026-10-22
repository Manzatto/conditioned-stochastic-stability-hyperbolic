module
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! An actual C1 compactly supported function is globally Lipschitz:
the derivative bound is constructed from its continuous compact support. -/
public noncomputable section
open Set
open scoped ContDiff BoundedContinuousFunction
namespace LeanShared.CompactC1Lipschitz
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_lipschitz (g : E → F) (smooth : ContDiff ℝ 1 g)
    (compact : HasCompactSupport g) : ∃ L : NNReal, LipschitzWith L g := by
  have derivativeCompact := (compact.fderiv ℝ).isCompact_range
    (smooth.continuous_fderiv (by norm_num))
  obtain ⟨R,hR,bound⟩ := derivativeCompact.isBounded.exists_pos_norm_le
  refine ⟨⟨R,hR.le⟩, lipschitzWith_of_nnnorm_fderiv_le
    (smooth.differentiable (by norm_num)) ?_⟩
  intro x
  have point := bound (fderiv ℝ g x) (mem_range_self x)
  exact_mod_cast point
end LeanShared.CompactC1Lipschitz
