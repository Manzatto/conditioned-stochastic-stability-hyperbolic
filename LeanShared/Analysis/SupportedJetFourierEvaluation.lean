module
public import LeanShared.Analysis.SupportedFiniteJetSpace
public import LeanShared.Analysis.CompactFiniteFourierControl
import Mathlib.Tactic

/-! Actual Fourier evaluation on the fixed-support finite jet Banach
space is a bounded linear map, with the polynomial spatial envelope
derived from its genuine derivatives. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform BoundedContinuousFunction
namespace LeanShared.SupportedJetFourierEvaluation
variable {Z:Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]

@[expose] def physical (n:ℕ) (K:Set Z):SupportedFiniteJetSpace.space n K→L[ℂ](Z→ᵇℂ):=
  (BoundedFiniteJetSpace.construct n (F:=ℂ)).physical.comp (SupportedFiniteJetSpace.space n K).subtypeL

theorem polynomial_bound (n:ℕ) {K:Set Z} (compact:IsCompact K)
    (q:SupportedFiniteJetSpace.space n K) (z:Z):
    (1+‖z‖)^n*‖𝓕 (fun w=>physical n K q w) z‖≤
      (4^n*((n+1:ℕ)*volume.real K))*‖q‖:=by
  have raw:=CompactFiniteFourierDecay.uniform_bound_of_derivatives compact
    (SupportedFiniteJetSpace.tsupport_subset n compact.isClosed q) n
    ((BoundedFiniteJetSpace.construct n (F:=ℂ)).regular q.val) ‖q‖
    (fun j hj x _=>BoundedFiniteJetSpace.derivative_le n q.val j hj x) z
  exact raw.trans_eq (by ring)

@[expose] def weight (z w:Z):ℂ:=Complex.exp ((-2*Real.pi*inner ℝ w z:ℝ)*Complex.I)

theorem integrable_weight (n:ℕ) {K:Set Z} (compact:IsCompact K)
    (q:SupportedFiniteJetSpace.space n K) (z:Z):
    Integrable (fun w=>weight z w*physical n K q w):=by
  have cw:Continuous (weight z):=by unfold weight;fun_prop
  exact (cw.mul (physical n K q).continuous).integrable_of_hasCompactSupport
    ((SupportedFiniteJetSpace.compact_support n compact q).mul_left)

theorem integral_eq_fourier (n:ℕ) (K:Set Z) (q:SupportedFiniteJetSpace.space n K) (z:Z):
    (∫w,weight z w*physical n K q w)=𝓕 (fun w=>physical n K q w) z:=by
  rw [Real.fourier_eq']
  rfl

@[expose] def evaluation (n:ℕ) {K:Set Z} (compact:IsCompact K) (z:Z):
    SupportedFiniteJetSpace.space n K→L[ℂ]ℂ:=
  LinearMap.mkContinuous
    { toFun:=fun q=>∫w,weight z w*physical n K q w
      map_add':=by
        intro q q'
        simp only [map_add,BoundedContinuousFunction.add_apply,mul_add]
        exact integral_add (integrable_weight n compact q z) (integrable_weight n compact q' z)
      map_smul':=by
        intro c q
        simp only [map_smul,BoundedContinuousFunction.smul_apply,smul_eq_mul]
        simp_rw [mul_left_comm (weight z _) c]
        exact integral_const_mul c _ }
    (4^n*((n+1:ℕ)*volume.real K)) (fun q=>by
      change ‖∫w,weight z w*physical n K q w‖≤_
      rw [integral_eq_fourier]
      have factor:1≤(1+‖z‖)^n:=one_le_pow₀ (by linarith [norm_nonneg z])
      exact (le_mul_of_one_le_left (norm_nonneg _) factor).trans (polynomial_bound n compact q z))

theorem evaluation_eq (n:ℕ) {K:Set Z} (compact:IsCompact K) (z:Z)
    (q:SupportedFiniteJetSpace.space n K):evaluation n compact z q=𝓕 (fun w=>physical n K q w) z:=
  integral_eq_fourier n K q z
end LeanShared.SupportedJetFourierEvaluation
