module
public import LeanShared.Analysis.ConeDyadicSymbols
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! The radial symbol cutoff and the compactly supported Schwartz test cutoff
are constructed from Mathlib smooth bumps, rather than assumed to exist. -/
public noncomputable section
open Set
open scoped SchwartzMap ContDiff
namespace LeanShared.ConstructedSchwartzCutoff
@[expose] def radialBump : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
@[expose] def radial : ConeDyadicSymbols.RadialCutoff where
  toFun := radialBump
  smooth := radialBump.contDiff
  one r inside := radialBump.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,radialBump] using inside)
  zero r outside := radialBump.zero_of_le_dist (by
    simpa only [Real.dist_eq,sub_zero,radialBump] using outside)
  even r := radialBump.neg r
  nonneg r := radialBump.nonneg
  le_one r := radialBump.le_one
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
@[expose] def bump (R : ℝ) (nonnegative : 0 ≤ R) : ContDiffBump (0:E) :=
  ⟨R+1,R+2,by linarith,by linarith⟩
@[expose] def cutoff (R : ℝ) (nonnegative : 0 ≤ R) : 𝓢(E,ℂ) :=
  ((bump (E:=E) R nonnegative).hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (bump (E:=E) R nonnegative).contDiff)

theorem one (R : ℝ) (nonnegative : 0 ≤ R) {x : E} (inside : ‖x‖ ≤ R) :
    cutoff R nonnegative x=1 := by
  change (((bump (E:=E) R nonnegative) x:ℝ):ℂ)=1
  rw [(bump (E:=E) R nonnegative).one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall,dist_zero_right,bump] using
      (show ‖x‖ ≤ R+1 by linarith))]
  rfl

theorem supported (R : ℝ) (nonnegative : 0 ≤ R) (x : E)
    (outside : x ∉ Metric.closedBall (0:E) (R+2)) : cutoff R nonnegative x=0 := by
  change (((bump (E:=E) R nonnegative) x:ℝ):ℂ)=0
  have large : R+2 ≤ ‖x‖ := le_of_lt (by
    simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using outside)
  rw [(bump (E:=E) R nonnegative).zero_of_le_dist (by simpa only [bump,dist_zero_right] using large)]
  rfl
end LeanShared.ConstructedSchwartzCutoff
