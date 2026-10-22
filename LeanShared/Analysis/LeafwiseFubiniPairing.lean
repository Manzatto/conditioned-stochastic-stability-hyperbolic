module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! A uniform L1 bound on actual parallel leaves controls ambient test
pairings by Fubini. This is a direct estimate for functions, not an assumed
distribution embedding. -/
public section
open MeasureTheory Filter
namespace LeanShared.LeafwiseFubiniPairing
variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
  (μ : Measure U) (ν : Measure V) [SFinite μ] [SFinite ν]

theorem bound (f test : U × V → ℂ) (A C : ℝ) (hC : 0 ≤ C)
    (w : V → ℝ) (nonnegative : ∀ v, 0 ≤ w v) (integrableW : Integrable w ν)
    (integrableProduct : Integrable (fun z => f z*test z) (μ.prod ν))
    (integrableLeaves : ∀ v, Integrable (fun u => f (u,v)) μ)
    (leafBound : ∀ v, (∫ u, ‖f (u,v)‖ ∂μ) ≤ A)
    (testBound : ∀ u v, ‖test (u,v)‖ ≤ C*w v) :
    ‖∫ z, f z*test z ∂μ.prod ν‖ ≤ (C*A)*(∫ v, w v ∂ν) := by
  have inner : ∀ᵐ v ∂ν, (∫ u, ‖f (u,v)*test (u,v)‖ ∂μ) ≤ (C*A)*w v := by
    filter_upwards [integrableProduct.prod_left_ae] with v hv
    calc
      _ ≤ ∫ u, (C*w v)*‖f (u,v)‖ ∂μ := by
        apply integral_mono_ae hv.norm ((integrableLeaves v).norm.const_mul (C*w v))
        exact Eventually.of_forall (fun u => by
          change ‖f (u,v)*test (u,v)‖ ≤ C*w v*‖f (u,v)‖
          rw [norm_mul,mul_comm (C*w v)]
          exact mul_le_mul_of_nonneg_left (testBound u v) (norm_nonneg _))
      _ = (C*w v)*(∫ u, ‖f (u,v)‖ ∂μ) := integral_const_mul _ _
      _ ≤ (C*w v)*A := mul_le_mul_of_nonneg_left (leafBound v)
        (mul_nonneg hC (nonnegative v))
      _ = (C*A)*w v := by ring
  calc
    _ ≤ ∫ z, ‖f z*test z‖ ∂μ.prod ν := norm_integral_le_integral_norm _
    _ = ∫ v, ∫ u, ‖f (u,v)*test (u,v)‖ ∂μ ∂ν :=
      integral_prod_symm _ integrableProduct.norm
    _ ≤ ∫ v, (C*A)*w v ∂ν := integral_mono_ae
      integrableProduct.norm.integral_prod_right (integrableW.const_mul (C*A)) inner
    _ = (C*A)*(∫ v, w v ∂ν) := integral_const_mul _ _
end LeanShared.LeafwiseFubiniPairing
