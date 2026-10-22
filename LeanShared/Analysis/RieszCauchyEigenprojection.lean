module
public import LeanShared.Analysis.CircleIntegralTwoPoles
public import LeanShared.Analysis.RieszCauchyShift
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity

/-! The actual resolvent Cauchy transform annihilates every interior
scalar eigenprojection, by exact cancellation of the two interior poles. -/
public noncomputable section
open Set Metric
namespace LeanShared.RieszCauchyEigenprojection
open RieszContourIdempotent ContourProjectorContinuity
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem resolvent_products (T p : A) (lam z : ℂ)
    (right : T*p=lam•p) (left : p*T=lam•p)
    (res : z ∈ resolventSet ℂ T) (different : z-lam ≠ 0) :
    resolvent T z*p=(z-lam)⁻¹•p ∧ p*resolvent T z=(z-lam)⁻¹•p := by
  have sP : (algebraMap ℂ A z-T)*p=(z-lam)•p := by
    simp only [sub_mul,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul,right,sub_smul]
  have pS : p*(algebraMap ℂ A z-T)=(z-lam)•p := by
    simp only [mul_sub,Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one,left,sub_smul]
  have inverseLeft : (algebraMap ℂ A z-T)*resolvent T z=1 := Ring.mul_inverse_cancel _ res
  have inverseRight : resolvent T z*(algebraMap ℂ A z-T)=1 := Ring.inverse_mul_cancel _ res
  have first : (z-lam)•(resolvent T z*p)=p := by
    rw [←mul_smul_comm,←sP,←mul_assoc,inverseRight,one_mul]
  have second : (z-lam)•(p*resolvent T z)=p := by
    rw [←smul_mul_assoc,←pS,mul_assoc,inverseLeft,mul_one]
  constructor
  · have scaled := congrArg (fun v : A => (z-lam)⁻¹•v) first
    simpa only [smul_smul,inv_mul_cancel₀ different,one_smul] using scaled
  · have scaled := congrArg (fun v : A => (z-lam)⁻¹•v) second
    simpa only [smul_smul,inv_mul_cancel₀ different,one_smul] using scaled

theorem annihilates (T p : A) (lam c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (right : T*p=lam•p) (left : p*T=lam•p)
    (res : sphere c R ⊆ resolventSet ℂ T) (inside : lam ∈ ball c R)
    (w : ℂ) (hw : w ∈ ball c R) :
    cauchyTransform T c R w*p=0 ∧ p*cauchyTransform T c R w=0 := by
  let G := fun z : ℂ => (z-w)⁻¹•resolvent T z
  have nz (u : ℂ) (hu : u ∈ ball c R) : ∀ z ∈ sphere c R, z-u ≠ 0 := by
    intro z hz he
    have same := sub_eq_zero.mp he
    subst z
    exact (ne_of_lt hu) hz
  have continuousG : ContinuousOn G (sphere c R) :=
    ((continuousOn_id.sub continuousOn_const).inv₀ (nz w hw)).smul
      (fun z hz => (spectrum.hasDerivAt_resolvent_const_left (res hz)).continuousAt.continuousWithinAt)
  have integrable : CircleIntegrable G c R := continuousG.circleIntegrable hR
  have product (z : ℂ) (hz : z ∈ sphere c R) :
      G z*p=((z-w)⁻¹*(z-lam)⁻¹)•p ∧ p*G z=((z-w)⁻¹*(z-lam)⁻¹)•p := by
    have eigen := resolvent_products T p lam z right left (res hz) (nz lam inside z hz)
    constructor
    · change ((z-w)⁻¹•resolvent T z)*p=_
      rw [smul_mul_assoc,eigen.1,smul_smul]
    · change p*((z-w)⁻¹•resolvent T z)=_
      rw [mul_smul_comm,eigen.2,smul_smul]
  have scalar : (∮ z in C(c,R), ((z-w)⁻¹*(z-lam)⁻¹)•p)=0 := by
    rw [circleIntegral.integral_smul_const,
      CircleIntegralTwoPoles.integral_eq_zero c w lam R hR hw inside,zero_smul]
  have intRight : (∮ z in C(c,R), G z*p)=0 := by
    rw [circleIntegral.integral_congr hR (fun z hz => (product z hz).1)]
    exact scalar
  have intLeft : (∮ z in C(c,R), p*G z)=0 := by
    rw [circleIntegral.integral_congr hR (fun z hz => (product z hz).2)]
    exact scalar
  constructor
  · have mapped : (∮ z in C(c,R), G z)*p = ∮ z in C(c,R), G z*p :=
      map_circleIntegral ((ContinuousLinearMap.mul ℂ A).flip p) G c R integrable
    change ((2*Real.pi*Complex.I : ℂ)⁻¹•∮ z in C(c,R), G z)*p=0
    rw [smul_mul_assoc,mapped,intRight,smul_zero]
  · have mapped : p*(∮ z in C(c,R), G z) = ∮ z in C(c,R), p*G z :=
      map_circleIntegral (ContinuousLinearMap.mul ℂ A p) G c R integrable
    change p*((2*Real.pi*Complex.I : ℂ)⁻¹•∮ z in C(c,R), G z)=0
    rw [mul_smul_comm,mapped,intLeft,smul_zero]
end LeanShared.RieszCauchyEigenprojection
