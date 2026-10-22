module
public import LeanShared.Analysis.RegularisedPhaseIdentity
import Mathlib.Tactic

/-! Exact finite directional decomposition, retaining both regularized
terms before Fourier inversion and before taking absolute values. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace LeanShared.FiniteRegularisedPhaseIdentity
open NonstationaryPhaseIntegration
variable {E ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem identity (μ:Measure E) [μ.IsAddHaarMeasure]
    {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) (f:E→ℂ) (v:ι→E)
    (h k:ι→E→ℂ) (hc:∀i,Continuous (h i)) (hs:∀i,HasCompactSupport (h i))
    (kc:∀i,ContDiff ℝ 1 (k i)) (ks:∀i,HasCompactSupport (k i))
    (resolution:∀x,∑i,(fderiv ℝ φ x (v i):ℂ)*h i x=f x)
    (Λ:ℝ) (hΛ:Λ≠0):
    -Complex.I*(∫x,oscillation Λ φ x*f x ∂μ)=
      (Λ:ℂ)⁻¹*(∑i,∫x,oscillation Λ φ x*fderiv ℝ (k i) x (v i) ∂μ)+
      -Complex.I*(∑i,∫x,oscillation Λ φ x*(fderiv ℝ φ x (v i):ℂ)*(h i x-k i x) ∂μ):=by
  have split:(∫x,oscillation Λ φ x*f x ∂μ)=
      ∑i,∫x,oscillation Λ φ x*(fderiv ℝ φ x (v i):ℂ)*h i x ∂μ:=by
    rw [←integral_finsetSum _ (fun i _=>RegularisedPhaseIdentity.integrable_directed μ hφ (hc i) (hs i) Λ (v i))]
    apply integral_congr_ae
    filter_upwards with x
    rw [←resolution x]
    simp only [Finset.mul_sum,mul_assoc]
  rw [split,Finset.mul_sum]
  calc
    _ = ∑i,((Λ:ℂ)⁻¹*(∫x,oscillation Λ φ x*fderiv ℝ (k i) x (v i) ∂μ)+
        -Complex.I*(∫x,oscillation Λ φ x*(fderiv ℝ φ x (v i):ℂ)*(h i x-k i x) ∂μ)):=by
      apply Finset.sum_congr rfl
      intro i _
      exact RegularisedPhaseIdentity.identity μ hφ (hc i) (hs i) (kc i) (ks i) Λ hΛ (v i)
    _ = _:=by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
end LeanShared.FiniteRegularisedPhaseIdentity
