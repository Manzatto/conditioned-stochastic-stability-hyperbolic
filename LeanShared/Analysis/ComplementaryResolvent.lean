module
public import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Tactic.Module

/-! Removing an invariant scalar spectral projection adds no nonzero
spectrum outside the original spectrum. The inverse is constructed. -/
public section
namespace LeanShared.ComplementaryResolvent
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem mem_resolvent (T p : A) (lam w : 𝕜) (idempotent : p*p=p)
    (right : T*p=lam•p) (left : p*T=lam•p) (hw : w ≠ 0)
    (res : w ∈ resolventSet 𝕜 T) : w ∈ resolventSet 𝕜 (T-lam•p) := by
  let s := algebraMap 𝕜 A w-T
  let t := algebraMap 𝕜 A w-(T-lam•p)
  let U := resolvent T w
  let q := 1-p
  have sU : s*U=1 := Ring.mul_inverse_cancel _ res
  have Us : U*s=1 := Ring.inverse_mul_cancel _ res
  have sp : s*p=p*s := by
    simp only [s,sub_mul,mul_sub,Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc,mul_smul_comm,one_mul,mul_one,right,left]
  have sq : s*q=q*s := by simp only [q,mul_sub,sub_mul,mul_one,one_mul,sp]
  have Uq : U*q=q*U := by
    calc
      U*q = U*q*(s*U) := by rw [sU,mul_one]
      _ = U*(q*s)*U := by simp only [mul_assoc]
      _ = U*(s*q)*U := by rw [sq]
      _ = q*U := by rw [←mul_assoc U s q,Us,one_mul]
  have pq : p*q=0 := by dsimp only [q]; rw [mul_sub,mul_one,idempotent,sub_self]
  have qp : q*p=0 := by dsimp only [q]; rw [sub_mul,one_mul,idempotent,sub_self]
  have ts : t=s+lam•p := by dsimp only [t,s]; module
  have tq : t*q=s*q := by rw [ts,add_mul,smul_mul_assoc,pq,smul_zero,add_zero]
  have qt : q*t=q*s := by rw [ts,mul_add,mul_smul_comm,qp,smul_zero,add_zero]
  have tp : t*p=w•p := by
    dsimp only [t]
    simp only [sub_mul,smul_mul_assoc,idempotent,right,sub_self,sub_zero,
      Algebra.algebraMap_eq_smul_one,one_mul]
  have pt : p*t=w•p := by
    dsimp only [t]
    simp only [mul_sub,mul_smul_comm,idempotent,left,sub_self,sub_zero,
      Algebra.algebraMap_eq_smul_one,mul_one]
  have first : t*(U*q)=q := by
    rw [Uq,←mul_assoc,tq,sq,mul_assoc,sU,mul_one]
  have second : (U*q)*t=q := by
    rw [mul_assoc,qt,←sq,←mul_assoc,Us,one_mul]
  have firstP : t*(w⁻¹•p)=p := by rw [mul_smul_comm,tp,smul_smul,inv_mul_cancel₀ hw,one_smul]
  have secondP : (w⁻¹•p)*t=p := by rw [smul_mul_assoc,pt,smul_smul,inv_mul_cancel₀ hw,one_smul]
  have hleft : t*(U*q+w⁻¹•p)=1 := by rw [mul_add,first,firstP]; exact sub_add_cancel 1 p
  have hright : (U*q+w⁻¹•p)*t=1 := by rw [add_mul,second,secondP]; exact sub_add_cancel 1 p
  exact spectrum.mem_resolventSet_of_left_right_inverse hleft hright
end LeanShared.ComplementaryResolvent
