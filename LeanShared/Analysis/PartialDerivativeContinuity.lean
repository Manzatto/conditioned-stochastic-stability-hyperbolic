module
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Joint C¹ regularity gives continuity of the actual spatial derivative
on an open parameter/state domain, with no stronger parameter topology. -/
public noncomputable section
open Set
namespace LeanShared.PartialDerivativeContinuity
variable {P E F:Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem partial_eq {H:P×E→F} {z:P×E} (h:DifferentiableAt ℝ H z) :
    fderiv ℝ (fun x=>H (z.1,x)) z.2=
      (fderiv ℝ H z).comp (ContinuousLinearMap.inr ℝ P E) := by
  have pair : HasFDerivAt (fun x:E=>(z.1,x)) (ContinuousLinearMap.inr ℝ P E) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  exact (h.hasFDerivAt.comp z.2 pair).fderiv

 theorem continuousOn_partial {H:P×E→F} {U:Set (P×E)} (openU:IsOpen U)
    (h:ContDiffOn ℝ 1 H U) :
    ContinuousOn (fun z:P×E=>fderiv ℝ (fun x=>H (z.1,x)) z.2) U := by
  have control : ContinuousOn (fun z:P×E=>(fderiv ℝ H z).comp (ContinuousLinearMap.inr ℝ P E)) U := by
    intro z hz
    exact (((h z hz).contDiffAt (openU.mem_nhds hz)).continuousAt_fderiv (by norm_num)).clm_comp
      continuousAt_const |>.continuousWithinAt
  apply control.congr
  intro z hz
  exact (partial_eq (((h z hz).contDiffAt (openU.mem_nhds hz)).differentiableAt (by norm_num)))
end LeanShared.PartialDerivativeContinuity
