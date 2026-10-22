module
public import LeanShared.Geometry.BoundedDerivativeGraph
public import LeanShared.Geometry.CompactSupportBoundedFunction
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic

/-! Complete bounded finite derivative graphs. Compatibility is an actual
Fréchet derivative relation and is closed under uniform limits; the norm
is controlled by the actual finite family of derivative sup norms. -/
public noncomputable section
open Set
open scoped ContDiff BoundedContinuousFunction
namespace LeanShared.BoundedFiniteJetSpace
universe u
variable (E F:Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] [CompleteSpace F]

structure Model (n:ℕ) where
  carrier:Type u
  [normed:NormedAddCommGroup carrier]
  [scalar:NormedSpace ℂ carrier]
  [complete:CompleteSpace carrier]
  physical:carrier→L[ℂ](E→ᵇF)
  faithful:Function.Injective physical
  regular:∀v,ContDiff ℝ (n:ℕ∞ω) (physical v)
  represents:∀f:E→F,ContDiff ℝ ∞ f→HasCompactSupport f→
    ∃v:carrier,∀x,physical v x=f x
attribute [instance] Model.normed Model.scalar Model.complete
variable {E F}

@[expose] def base:Model E F 0 where
  carrier:=E→ᵇF
  physical:=ContinuousLinearMap.id ℂ _
  faithful:=Function.injective_id
  regular v:=contDiff_zero.mpr v.continuous
  represents f smooth compact:=⟨CompactSupportBoundedFunction.bounded f smooth.continuous compact,fun _=>rfl⟩

@[expose] def successor {n:ℕ} (d:Model E (E→L[ℝ]F) n):Model E F (n+1) where
  carrier:=BoundedDerivativeGraph.graph d.physical
  physical:=BoundedDerivativeGraph.physical d.physical
  faithful:=BoundedDerivativeGraph.physical_injective d.physical d.faithful
  regular v:=by
    have derivative:fderiv ℝ (BoundedDerivativeGraph.physical d.physical v)=d.physical v.val.2:=by
      funext x
      exact (BoundedDerivativeGraph.derivative d.physical v x).fderiv
    rw [show ((n+1:ℕ):ℕ∞ω)=(n:ℕ∞ω)+1 by simp]
    apply contDiff_succ_iff_fderiv.mpr
    refine ⟨(fun x=>(BoundedDerivativeGraph.derivative d.physical v x).differentiableAt),by simp,?_⟩
    rw [derivative]
    exact d.regular v.val.2
  represents f smooth compact:=by
    obtain ⟨w,rep⟩:=d.represents (fderiv ℝ f) (smooth.fderiv_right (by simp)) (compact.fderiv ℝ)
    let bf:=CompactSupportBoundedFunction.bounded f smooth.continuous compact
    have compatible:∀x,HasFDerivAt bf (d.physical w x) x:=by
      intro x
      rw [rep x]
      exact (smooth.differentiable (by simp) x).hasFDerivAt
    exact ⟨⟨(bf,w),compatible⟩,fun _=>rfl⟩

@[expose] def construct : (n:ℕ)→{F:Type u}→ [NormedAddCommGroup F]→ [NormedSpace ℝ F]→
    [NormedSpace ℂ F]→ [IsScalarTower ℝ ℂ F]→ [SMulCommClass ℝ ℂ F]→ [CompleteSpace F]→Model E F n
  | 0,F',_,_,_,_,_,_=>base (F:=F')
  | n+1,F',_,_,_,_,_,_=>successor (F:=F') (construct n (F:=E→L[ℝ]F'))

theorem norm_le : ∀n:ℕ,∀{F:Type u},∀[NormedAddCommGroup F],∀[NormedSpace ℝ F],
    ∀[NormedSpace ℂ F],∀[IsScalarTower ℝ ℂ F],∀[SMulCommClass ℝ ℂ F],∀[CompleteSpace F],
    ∀v:(construct (E:=E) n (F:=F)).carrier,∀B:ℝ,0≤B→
      (∀j≤n,∀x,‖iteratedFDeriv ℝ j ((construct n (F:=F)).physical v) x‖≤B)→‖v‖≤B:=by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ _ _ _ v B hB bound
    apply (BoundedContinuousFunction.norm_le hB).mpr
    intro x
    have raw:=bound 0 (by omega) x
    rw [norm_iteratedFDeriv_zero] at raw
    exact raw
  | succ n ih =>
    intro F _ _ _ _ _ _ v B hB bound
    let d:=construct (E:=E) n (F:=E→L[ℝ]F)
    have derivative:fderiv ℝ (BoundedDerivativeGraph.physical d.physical v)=d.physical v.val.2:=by
      funext x
      exact (BoundedDerivativeGraph.derivative d.physical v x).fderiv
    change max ‖v.val.1‖ ‖v.val.2‖≤B
    apply max_le
    · apply (BoundedContinuousFunction.norm_le hB).mpr
      intro x
      have raw:=bound 0 (by omega) x
      rw [norm_iteratedFDeriv_zero] at raw
      exact raw
    · apply ih v.val.2 B hB
      intro j hj x
      rw [←derivative,norm_iteratedFDeriv_fderiv]
      exact bound (j+1) (by omega) x
end LeanShared.BoundedFiniteJetSpace
