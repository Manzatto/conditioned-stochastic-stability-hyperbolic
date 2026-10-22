module
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The product of two interior simple-pole factors has zero circle integral,
including coincident poles. This is the complementary-resolvent cancellation. -/
public section
open Set Metric
namespace LeanShared.CircleIntegralTwoPoles

theorem integral_eq_zero (c u v : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hu : u ∈ ball c R) (hv : v ∈ ball c R) :
    (∮ z in C(c,R), (z-u)⁻¹*(z-v)⁻¹)=0 := by
  by_cases same : u=v
  · subst v
    have scalar := circleIntegral.integral_sub_zpow_of_ne (n := (-2 : ℤ)) (by decide) c u R
    simpa only [zpow_neg,zpow_two,mul_inv_rev] using scalar
  have neqU : ∀ z ∈ sphere c R, z-u ≠ 0 := by
    intro z hz
    apply sub_ne_zero.mpr
    intro he
    subst z
    exact (ne_of_lt hu) hz
  have neqV : ∀ z ∈ sphere c R, z-v ≠ 0 := by
    intro z hz
    apply sub_ne_zero.mpr
    intro he
    subst z
    exact (ne_of_lt hv) hz
  have intU : CircleIntegrable (fun z : ℂ => (z-u)⁻¹) c R :=
    ((continuousOn_id.sub continuousOn_const).inv₀ neqU).circleIntegrable hR
  have intV : CircleIntegrable (fun z : ℂ => (z-v)⁻¹) c R :=
    ((continuousOn_id.sub continuousOn_const).inv₀ neqV).circleIntegrable hR
  have identity : (∮ z in C(c,R), (z-u)⁻¹*(z-v)⁻¹) =
      ∮ z in C(c,R), (u-v)⁻¹*((z-u)⁻¹-(z-v)⁻¹) := by
    apply circleIntegral.integral_congr hR
    intro z hz
    field_simp [neqU z hz,neqV z hz,sub_ne_zero.mpr same]
    ring
  rw [identity,circleIntegral.integral_const_mul,circleIntegral.integral_sub intU intV,
    circleIntegral.integral_sub_inv_of_mem_ball hu,circleIntegral.integral_sub_inv_of_mem_ball hv,
    sub_self,mul_zero]
end LeanShared.CircleIntegralTwoPoles
