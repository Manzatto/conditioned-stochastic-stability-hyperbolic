module
public import LeanShared.Geometry.BanachValuedHolderGraph
public import LeanShared.Geometry.BoundedDerivativeGraph
public import LeanShared.Geometry.HolderFractionalRegularity
public import LeanShared.Geometry.FractionalDerivativeSuccessor
public import LeanShared.Geometry.CompactSupportBoundedFunction
public import LeanShared.Analysis.CompactC1Lipschitz
public import LeanShared.Analysis.BoundedLipschitzHolder

/-! Actual complete bounded C^(n+a) derivative graphs at every integer order.
Each level imposes HasFDerivAt compatibility with the previous level; jets
and their compatibility are constructed, never independent source fields. -/
public noncomputable section
open Set
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.HigherDerivativeHolderSpace
universe u
variable (E F:Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] [CompleteSpace F]

structure Model (r:ℝ) where
  carrier:Type u
  [normed:NormedAddCommGroup carrier]
  [scalar:NormedSpace ℂ carrier]
  [complete:CompleteSpace carrier]
  physical:carrier→L[ℂ](E→ᵇF)
  faithful:Function.Injective physical
  physical_norm_le:∀v,‖physical v‖≤‖v‖
  regular:∀v,FractionalManifoldRegularity.Regular (E:=E) (F:=F) r (physical v)
  represents_smooth:∀ (f:E→F),ContDiff ℝ ∞ f→HasCompactSupport f→
    ∃v:carrier,∀x,physical v x=f x
attribute [instance] Model.normed Model.scalar Model.complete

variable {E F}
@[expose] def base {a:ℝ} (ha:0<a) (ha1:a<1) : Model E F a where
  carrier:=BanachValuedHolderGraph.graph E F a
  physical:=BanachValuedHolderGraph.physical E F a
  faithful:=BanachValuedHolderGraph.physical_injective E F a
  physical_norm_le v:=norm_fst_le v.val
  regular v:=FractionalManifoldRegularity.regular_of_holder ha ha1
    (BanachValuedHolderGraph.physical E F a v).continuous (norm_nonneg v)
    (fun x y=>by simpa only [dist_eq_norm] using BanachValuedHolderGraph.increment_bound E F a v x y)
  represents_smooth f smooth compact:=by
    let bounded:=CompactSupportBoundedFunction.bounded f smooth.continuous compact
    obtain ⟨L,lip⟩:=CompactC1Lipschitz.exists_lipschitz f
      (smooth.of_le (by simp)) compact
    let C:=max (L:ℝ) (2*‖bounded‖)
    have bound:∀x y,‖bounded x-bounded y‖≤C*dist x y^a:=
      BoundedLipschitzHolder.bound bounded lip ha.le ha1.le
    refine ⟨BanachValuedHolderGraph.ofBound E F a bounded C bound,?_⟩
    intro x
    rw [BanachValuedHolderGraph.physical_ofBound]
    rfl

@[expose] def successor {r:ℝ} (d:Model E (E→L[ℝ]F) r) : Model E F (r+1) where
  carrier:=BoundedDerivativeGraph.graph d.physical
  physical:=BoundedDerivativeGraph.physical d.physical
  faithful:=BoundedDerivativeGraph.physical_injective d.physical d.faithful
  physical_norm_le v:=norm_fst_le v.val
  regular v:=by
    have derivative: fderiv ℝ (BoundedDerivativeGraph.physical d.physical v)=d.physical v.val.2 := by
      funext x
      exact (BoundedDerivativeGraph.derivative d.physical v x).fderiv
    apply FractionalManifoldRegularity.regular_of_regular_fderiv
      (fun x=>(BoundedDerivativeGraph.derivative d.physical v x).differentiableAt)
    rw [derivative]
    exact d.regular v.val.2
  represents_smooth f smooth compact:=by
    obtain ⟨w,represents⟩:=d.represents_smooth (fderiv ℝ f)
      (smooth.fderiv_right (by simp)) (compact.fderiv ℝ)
    let bounded:=CompactSupportBoundedFunction.bounded f smooth.continuous compact
    have compatible:∀x,HasFDerivAt bounded (d.physical w x) x:=by
      intro x
      rw [represents x]
      exact (smooth.differentiable (by simp) x).hasFDerivAt
    refine ⟨⟨(bounded,w),compatible⟩,fun _=>rfl⟩

/-- Change only the regularity label, preserving the actual carrier and norms
by definition. Avoid transporting the entire dependent model record. -/
@[expose] def Model.regrade {r s:ℝ} (d:Model E F r) (equal:r=s) : Model E F s where
  carrier:=d.carrier
  normed:=d.normed
  scalar:=d.scalar
  complete:=d.complete
  physical:=d.physical
  faithful:=d.faithful
  physical_norm_le:=d.physical_norm_le
  regular v:=equal ▸ d.regular v
  represents_smooth:=d.represents_smooth

@[expose] def construct {a:ℝ} (ha:0<a) (ha1:a<1) :
    (n:ℕ)→ {F:Type u}→ [NormedAddCommGroup F]→ [NormedSpace ℝ F]→ [NormedSpace ℂ F]→
      [IsScalarTower ℝ ℂ F]→ [SMulCommClass ℝ ℂ F]→ [CompleteSpace F]→ Model E F (a+n)
  | 0,F',_,_,_,_,_,_=>(base (E:=E) (F:=F') ha ha1).regrade (by simp)
  | n+1,F',_,_,_,_,_,_=>by
    exact (successor (F:=F') (construct ha ha1 n (F:=E→L[ℝ]F'))).regrade
      (by simp only [Nat.cast_add,Nat.cast_one,add_assoc])
end LeanShared.HigherDerivativeHolderSpace
