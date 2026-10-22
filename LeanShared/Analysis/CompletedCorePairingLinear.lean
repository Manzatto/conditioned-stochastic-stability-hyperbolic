module
public import LeanShared.Analysis.CompletedCorePairing
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The completed core pairing is linear in the test and bounded in operator norm. -/
public noncomputable section
namespace LeanShared.CompletedCorePairing
variable {Core B Test : Type*}
  [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [AddCommGroup Test] [Module ℂ Test]
  (q : Core →ₗ[ℂ] B) (p : Core →ₗ[ℂ] (Test →ₗ[ℂ] ℂ))
  (bounded : ∀ test, ∃ C : ℝ, ∀ f, ‖p f test‖ ≤ C * ‖q f‖)

include bounded in
theorem atTest_sub (v w : Test) : atTest q p (v - w) = atTest q p v - atTest q p w := by
  apply ContinuousLinearMap.ext
  intro z
  rw [sub_apply, sub_eq_add_neg, add q p bounded,
    show -w = (-1 : ℂ) • w by rw [neg_one_smul], smul q p bounded, neg_one_smul, ← sub_eq_add_neg]

theorem atTest_norm_le (test : Test) (C : ℝ) (hC : 0 ≤ C) (estimate : ∀ f, ‖p f test‖ ≤ C * ‖q f‖) :
    ‖atTest q p test‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC fun z => bound q p test C estimate z

include bounded in
/-- On a dense regular realization, the completed pairing equals any continuous functional
agreeing with the core pairing. -/
theorem atTest_eq_of_dense {Reg : Type*} [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
    (R : Reg →L[ℂ] DyadicCompletion.closedCore q) (regularCore : Core →ₗ[ℂ] Reg)
    (dense : DenseRange regularCore)
    (hR : ∀ c, R (regularCore c) = DyadicCompletion.coreLift q c)
    (test : Test) (Φ : Reg →L[ℂ] ℂ) (hΦ : ∀ c, Φ (regularCore c) = p c test) (r : Reg) :
    atTest q p test (R r) = Φ r := by
  have same : (fun r => atTest q p test (R r)) = fun r => Φ r :=
    dense.equalizer ((atTest q p test).comp R).continuous Φ.continuous (funext fun c => by
      simp only [Function.comp_apply]
      rw [hR, core q p bounded, hΦ])
  exact congrFun same r

/-- Weighted integrals transported through a continuous linear lift. -/
theorem integral_lift {Y X Z : Type*} [MeasurableSpace Y] (ν : MeasureTheory.Measure Y)
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    (Λ : Z →L[ℂ] X) (coef : Y → ℂ) (u : Y → Z)
    (hint : MeasureTheory.Integrable (fun y => coef y • u y) ν) (w : Y → X)
    (hw : ∀ y, Λ (u y) = w y) (zF : Z) (ident : ∫ y, coef y • u y ∂ν = zF) :
    ∫ y, coef y • w y ∂ν = Λ zF := by
  have same : (fun y => coef y • w y) = fun y => Λ (coef y • u y) :=
    funext fun y => by rw [map_smul, hw]
  rw [same, ContinuousLinearMap.integral_comp_comm Λ hint, ident]

/-- Scalar-weighted integrals commute with a continuous linear map. -/
theorem integral_smul_comp {Y X : Type*} [MeasurableSpace Y] (ν : MeasureTheory.Measure Y)
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (P : X →L[ℂ] X) (coef : Y → ℂ) (w : Y → X)
    (hint : MeasureTheory.Integrable (fun y => coef y • w y) ν) :
    ∫ y, coef y • P (w y) ∂ν = P (∫ y, coef y • w y ∂ν) := by
  have same : (fun y => coef y • P (w y)) = fun y => P (coef y • w y) :=
    funext fun y => (map_smul P (coef y) (w y)).symm
  rw [same, ContinuousLinearMap.integral_comp_comm P hint]

end LeanShared.CompletedCorePairing
