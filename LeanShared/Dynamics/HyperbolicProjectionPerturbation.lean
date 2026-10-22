module
public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.GCongr

/-! The actual stable/unstable off-diagonal projection block satisfies a
quadratically contracting perturbation estimate. Only algebraic invariance
and actual stable/inverse-unstable operator bounds are used. -/
public section
namespace LeanShared.HyperbolicProjectionPerturbation
variable {R:Type*} [NormedRing R]

theorem cross_bound (a ai b p q p' q':R)
    (inverse:ai*a=1) (invariant:p'*a=a*p) (otherInvariant:q'*b=b*q)
    (idempotent:p'*p'=p') (otherIdempotent:q*q=q)
    (κ B:ℝ)
    (unstable:‖ai*(1-p')‖≤κ) (stable:‖b*q‖≤κ) (projection:‖q‖≤B) :
    ‖(1-p)*q‖≤κ*B*‖a-b‖+κ^2*‖q'-p'‖ := by
  have nonnegativeκ:0≤κ := (norm_nonneg _).trans unstable
  have image:q'*(b*q)=b*q := by
    rw [←mul_assoc,otherInvariant,mul_assoc,otherIdempotent]
  have annihilate:(1-p')*p'=0 := by rw [sub_mul,one_mul,idempotent,sub_self]
  have split:b*q=(q'-p')*(b*q)+p'*(b*q) := by rw [sub_mul,sub_add_cancel,image]
  have cut:(1-p')*(b*q)=(1-p')*((q'-p')*(b*q)) := by
    have zero:(1-p')*(p'*(b*q))=0 := by rw [←mul_assoc,annihilate,zero_mul]
    calc
      _=(1-p')*((q'-p')*(b*q)+p'*(b*q)) := congrArg (fun x=>(1-p')*x) split
      _=_ := by rw [mul_add,zero,add_zero]
  have conjugate:(ai*(1-p'))*a=1-p := by
    rw [mul_assoc,sub_mul,one_mul,invariant,mul_sub,inverse,←mul_assoc,inverse,one_mul]
  let D:=ai*(1-p')
  have second:D*(b*q)=D*((q'-p')*(b*q)) := by
    simpa only [D,mul_assoc] using congrArg (fun x=>ai*x) cut
  have decomposition:(1-p)*q=D*((a-b)*q)+D*((q'-p')*(b*q)) := by
    calc
      _=D*(a*q) := by dsimp only [D]; rw [←mul_assoc,conjugate]
      _=D*((a-b)*q+b*q) := by congr 1; noncomm_ring
      _=_ := by rw [mul_add,second]
  have firstBound:‖D*((a-b)*q)‖≤κ*(‖a-b‖*B) := by
    calc
      _≤‖D‖*(‖a-b‖*‖q‖) := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _≤_ := by gcongr
  have secondBound:‖D*((q'-p')*(b*q))‖≤κ*(‖q'-p'‖*κ) := by
    calc
      _≤‖D‖*(‖q'-p'‖*‖b*q‖) := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _≤_ := by gcongr
  rw [decomposition]
  exact (norm_add_le _ _).trans ((add_le_add firstBound secondBound).trans_eq (by ring))

end LeanShared.HyperbolicProjectionPerturbation
