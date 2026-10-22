module
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Tactic

/-! Actual frequencyDerivative frequency derivatives of a jointly smooth symbol have
constructed compact value and Lipschitz bounds. This supplies Holder
control after substitution of a physical Holder matrix field. -/
public noncomputable section
open Set
open scoped ContDiff
namespace LeanShared.SmoothPartialDerivativeBounds
variable {A Z F:Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[expose] def frequencyDerivative (n:ℕ) (f:A × Z→F) (p:A × Z):
    ContinuousMultilinearMap ℝ (fun _ : Fin n=>Z) F:=
  iteratedFDeriv ℝ n (fun z=>f (p.1,z)) p.2

theorem representation (n:ℕ) (f:A × Z→F) (smooth:ContDiff ℝ ∞ f) (p:A × Z):
    frequencyDerivative n f p=(iteratedFDeriv ℝ n f p).compContinuousLinearMap
      (fun _=>ContinuousLinearMap.inr ℝ A Z):=by
  let shifted:A × Z→F:=fun q=>f (q+(p.1,0))
  have shiftedSmooth:ContDiff ℝ ∞ shifted:=smooth.comp (contDiff_id.add contDiff_const)
  have identity:(fun z=>f (p.1,z))=shifted∘ContinuousLinearMap.inr ℝ A Z:=by
    funext z
    simp only [shifted,Function.comp_apply,ContinuousLinearMap.inr_apply,Prod.add_def,zero_add,add_zero]
  dsimp only [frequencyDerivative]
  rw [identity,ContinuousLinearMap.iteratedFDeriv_comp_right _ shiftedSmooth _ (by simp)]
  dsimp only [shifted]
  rw [iteratedFDeriv_comp_add_right]
  simp only [ContinuousLinearMap.inr_apply,Prod.add_def,zero_add,add_zero,Prod.mk.eta]

theorem smooth_partial (n:ℕ) (f:A × Z→F) (smooth:ContDiff ℝ ∞ f):
    ContDiff ℝ ∞ (frequencyDerivative n f):=by
  have identity:frequencyDerivative n f=
      (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜:=ℝ) (F:=F)
        (fun _ : Fin n=>ContinuousLinearMap.inr ℝ A Z))∘iteratedFDeriv ℝ n f:=
    funext (representation n f smooth)
  rw [identity]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin n=>ContinuousLinearMap.inr ℝ A Z)).contDiff.comp
      (smooth.iteratedFDeriv_right (m:=∞) (by simp))

theorem compact_bounds (n:ℕ) (f:A × Z→F) (smooth:ContDiff ℝ ∞ f)
    {K:Set (A × Z)} (compact:IsCompact K) (convex:Convex ℝ K):
    ∃B L:ℝ,0≤B ∧ 0≤L ∧ (∀p∈K,‖frequencyDerivative n f p‖≤B) ∧
      ∀p∈K,∀q∈K,‖frequencyDerivative n f p-frequencyDerivative n f q‖≤L*‖p-q‖:=by
  have regular:=smooth_partial n f smooth
  obtain ⟨B,hB,value⟩:=(compact.image regular.continuous).isBounded.exists_pos_norm_le
  obtain ⟨L,hL,derivative⟩:=(compact.image (regular.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨B,L,hB.le,hL.le,(fun p hp=>value _ (mem_image_of_mem _ hp)),?_⟩
  intro p hp q hq
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _=>regular.differentiable (by simp) x)
    (fun x hx=>derivative _ (mem_image_of_mem _ hx)) convex hq hp
end LeanShared.SmoothPartialDerivativeBounds
