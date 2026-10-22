module
public import LeanShared.Analysis.RieszCauchyEigenprojection
public import LeanShared.Analysis.ComplementaryResolvent
import all LeanShared.Analysis.RieszContourIdempotent
import Mathlib.Tactic.Module

/-! Exact complementary Riesz spectral splitting, by a constructed two-sided
inverse on the whole contour interior; no point-spectrum restriction is used. -/
public noncomputable section
open Set Metric
namespace LeanShared.RieszComplementResolvent
open RieszContourIdempotent
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem interior (T : A) (c lam : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (res : sphere c R ⊆ resolventSet ℂ T) (inside : lam ∈ ball c R)
    (idempotent : projector T c R*projector T c R=projector T c R)
    (right : T*projector T c R=lam•projector T c R)
    (left : projector T c R*T=lam•projector T c R)
    (w : ℂ) (hw : w ∈ ball c R) (nonzero : w ≠ 0) :
    w ∈ resolventSet ℂ (T-lam•projector T c R) := by
  let p := projector T c R
  let H := cauchyTransform T c R w
  let s := algebraMap ℂ A w-T
  let t := algebraMap ℂ A w-(T-lam•p)
  have pp : p*p=p := idempotent
  have Tp : T*p=lam•p := right
  have pT : p*T=lam•p := left
  have shifted := RieszCauchyShift.identities T c R hR res w hw
  have annihilates := RieszCauchyEigenprojection.annihilates T p lam c R hR right left res inside w hw
  have ts : t=s+lam•p := by dsimp only [t,s]; module
  have tH : t*H=1-p := by
    rw [ts,add_mul,smul_mul_assoc,annihilates.2,smul_zero,add_zero]
    exact shifted.1
  have Ht : H*t=1-p := by
    rw [ts,mul_add,mul_smul_comm,annihilates.1,smul_zero,add_zero]
    exact shifted.2
  have tp : t*p=w•p := by
    dsimp only [t]
    simp only [sub_mul,smul_mul_assoc,pp,Tp,sub_self,sub_zero,
      Algebra.algebraMap_eq_smul_one,one_mul]
  have pt : p*t=w•p := by
    dsimp only [t]
    simp only [mul_sub,mul_smul_comm,pp,pT,sub_self,sub_zero,
      Algebra.algebraMap_eq_smul_one,mul_one]
  have firstP : t*(w⁻¹•p)=p := by rw [mul_smul_comm,tp,smul_smul,inv_mul_cancel₀ nonzero,one_smul]
  have secondP : (w⁻¹•p)*t=p := by rw [smul_mul_assoc,pt,smul_smul,inv_mul_cancel₀ nonzero,one_smul]
  have inverseLeft : t*(w⁻¹•p+H)=1 := by rw [mul_add,firstP,tH,add_sub_cancel]
  have inverseRight : (w⁻¹•p+H)*t=1 := by rw [add_mul,secondP,Ht,add_sub_cancel]
  exact spectrum.mem_resolventSet_of_left_right_inverse inverseLeft inverseRight

end LeanShared.RieszComplementResolvent
