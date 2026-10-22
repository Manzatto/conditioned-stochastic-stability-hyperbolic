module
public import LeanShared.Geometry.HigherDerivativeHolderSpace
public import LeanShared.Geometry.BanachEuclideanFractionalHolder
public import LeanShared.Geometry.FractionalDerivativePredecessor

/-! Every actual compact C^(n+a) function is represented in the constructed
complete derivative graph. This is the full bounded graph, with no claim
that smooth functions are dense at the same exponent. -/
public noncomputable section
open Set
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.HigherDerivativeHolderSpace
universe u
variable (E F:Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]

structure FullModel (r:ℝ) extends Model E F r where
  represents_regular:∀ (f:E→F),FractionalManifoldRegularity.Regular (E:=E) (F:=F) r f→
    HasCompactSupport f→∃v:carrier,∀x,physical v x=f x

variable {E F} [FiniteDimensional ℝ E]
  [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] [CompleteSpace F]

@[expose] def fullBase {a:ℝ} (ha:0<a) (ha1:a<1) : FullModel E F a where
  toModel:=base ha ha1
  represents_regular f regular compact:=by
    let bounded:=CompactSupportBoundedFunction.bounded f regular.differentiable.continuous compact
    obtain ⟨C,_,bound⟩:=FractionalManifoldRegularity.global_holder_of_regular_banach
      bounded compact ha ha1 regular
    have estimate:∀x y,‖bounded x-bounded y‖≤C*dist x y^a:=by
      simpa only [dist_eq_norm] using bound
    refine ⟨BanachValuedHolderGraph.ofBound E F a bounded C estimate,?_⟩
    intro x
    change BanachValuedHolderGraph.physical E F a
      (BanachValuedHolderGraph.ofBound E F a bounded C estimate) x=f x
    rw [BanachValuedHolderGraph.physical_ofBound]
    rfl

@[expose] def fullSuccessor {r:ℝ} (d:FullModel E (E→L[ℝ]F) r) : FullModel E F (r+1) where
  toModel:=successor d.toModel
  represents_regular f regular compact:=by
    have hr:0≤r:=(d.regular 0).nonnegative
    have derivativeRegular:=FractionalManifoldRegularity.regular_fderiv_of_regular hr regular
    obtain ⟨w,represents⟩:=d.represents_regular (fderiv ℝ f) derivativeRegular (compact.fderiv ℝ)
    have smooth:ContDiff ℝ 1 f:=by
      have floor:1≤⌊r+1⌋₊:=(Nat.one_le_floor_iff (r+1)).mpr (by linarith)
      exact regular.differentiable.contDiff.of_le (by exact_mod_cast floor)
    let bounded:=CompactSupportBoundedFunction.bounded f smooth.continuous compact
    have compatible:∀x,HasFDerivAt bounded (d.physical w x) x:=by
      intro x
      rw [represents x]
      exact (smooth.differentiable (by norm_num) x).hasFDerivAt
    refine ⟨⟨(bounded,w),compatible⟩,fun _=>rfl⟩

@[expose] def FullModel.regrade {r s:ℝ} (d:FullModel E F r) (equal:r=s) : FullModel E F s where
  toModel:=d.toModel.regrade equal
  represents_regular f regular compact:=d.represents_regular f (equal.symm ▸ regular) compact

@[expose] def constructFull {a:ℝ} (ha:0<a) (ha1:a<1) :
    (n:ℕ)→ {F:Type u}→ [NormedAddCommGroup F]→ [NormedSpace ℝ F]→ [NormedSpace ℂ F]→
      [IsScalarTower ℝ ℂ F]→ [SMulCommClass ℝ ℂ F]→ [CompleteSpace F]→ FullModel E F (a+n)
  | 0,F',_,_,_,_,_,_=>(fullBase (E:=E) (F:=F') ha ha1).regrade (by simp)
  | n+1,F',_,_,_,_,_,_=>by
    exact (fullSuccessor (F:=F') (constructFull ha ha1 n (F:=E→L[ℝ]F'))).regrade
      (by simp only [Nat.cast_add,Nat.cast_one,add_assoc])
end LeanShared.HigherDerivativeHolderSpace
