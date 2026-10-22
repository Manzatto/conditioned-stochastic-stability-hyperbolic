module
public import LeanShared.Analysis.HolderIncrementContinuity
public import LeanShared.Analysis.UniformBilinearHolder
public import LeanShared.Analysis.SupportedJetFourierEvaluation
import Mathlib.Tactic

/-! Multiplying the compatible frequency jet by the physical amplitude
retains compact physical support and derives the required Holder bound. -/
public noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace LeanShared.CompactHolderAmplitude
variable {E F:Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

theorem exists_amplitude (g:E→ℂ) (gc:Continuous g) (gs:HasCompactSupport g)
    (q:E→ᵇF) {a G H B C:ℝ} (hG:0≤G) (hH:0≤H)
    (gv:∀x,‖g x‖≤G) (gh:∀x y,‖g x-g y‖≤H*‖x-y‖^a)
    (qv:∀x,‖q x‖≤B) (qh:∀x y,‖q x-q y‖≤C*‖x-y‖^a):
    ∃f:E→ᵇF,(∀x,f x=g x • q x) ∧HasCompactSupport (fun x=>f x) ∧
      (∀x,‖f x‖≤G*B) ∧∀x y,‖f x-f y‖≤(G*C+H*B)*‖x-y‖^a:=by
  let f:E→F:=fun x=>g x • q x
  have fc:Continuous f:=gc.smul q.continuous
  have fv (x:E):‖f x‖≤G*B:=by
    rw [norm_smul]
    exact mul_le_mul (gv x) (qv x) (norm_nonneg _) hG
  have fh (x y:E):‖f x-f y‖≤(G*C+H*B)*‖x-y‖^a:=by
    have split:f x-f y=g x • (q x-q y)+(g x-g y) • q y:=by
      dsimp [f];simp only [smul_sub,sub_smul];abel
    rw [split]
    calc
      _ ≤ _:=norm_add_le _ _
      _ = ‖g x‖*‖q x-q y‖+‖g x-g y‖*‖q y‖:=by rw [norm_smul,norm_smul]
      _ ≤ G*(C*‖x-y‖^a)+(H*‖x-y‖^a)*B:=add_le_add
        (mul_le_mul (gv x) (qh x y) (norm_nonneg _) hG)
        (mul_le_mul (gh x y) (qv y) (norm_nonneg _) (by positivity))
      _ = _:=by ring
  let fb:E→ᵇF:=BoundedContinuousFunction.ofNormedAddCommGroup f fc (G*B) fv
  refine ⟨fb,fun _=>rfl,?_,fv,fh⟩
  apply HasCompactSupport.intro gs
  intro x hx
  change g x • q x=0
  rw [image_eq_zero_of_notMem_tsupport hx,zero_smul]
end LeanShared.CompactHolderAmplitude
