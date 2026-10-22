module
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! The actual resolvent is analytic on its resolvent set. -/
public noncomputable section
namespace LeanShared.AnalyticResolvent
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem analyticAt (P : A) {z : ℂ} (hz : z ∈ resolventSet ℂ P) :
    AnalyticAt ℂ (resolvent P) z := by
  have scalar : AnalyticAt ℂ (fun w : ℂ => w) z := analyticAt_id
  have one : AnalyticAt ℂ (fun _ : ℂ => (1 : A)) z := analyticAt_const
  have constant : AnalyticAt ℂ (fun _ : ℂ => P) z := analyticAt_const
  have shift : AnalyticAt ℂ (fun w : ℂ => algebraMap ℂ A w - P) z := by
    convert (scalar.smul one).sub constant using 1
    ext w
    change algebraMap ℂ A w - P = w • (1 : A) - P
    rw [Algebra.algebraMap_eq_smul_one]
  have inverse := analyticAt_inverse (𝕜 := ℂ) hz.unit
  rw [hz.unit_spec] at inverse
  exact inverse.comp (f := fun w : ℂ => algebraMap ℂ A w - P) shift

theorem analyticOnNhd (P : A) : AnalyticOnNhd ℂ (resolvent P) (resolventSet ℂ P) :=
  fun _ hz => analyticAt P hz
end LeanShared.AnalyticResolvent
