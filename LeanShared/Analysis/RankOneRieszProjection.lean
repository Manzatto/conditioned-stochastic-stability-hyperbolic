module

public import LeanShared.Analysis.RankOneResolventResidue
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Positivity

/-! The constructed rank-one projector equals the literal operator-valued
Riesz contour integral. All inverse, residue, and circle-integral identities
are proved from compactness/algebraic simplicity, rather than assumed. -/

public section
open Filter Set Metric
open scoped Topology
namespace LeanShared.RankOneResolvent
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The Riesz contour formula on any punctured resolvent disk for a simple pole. -/
theorem circle_integral_eq (a p : A) (μ : ℂ) (R : ℝ) (hR : 0 < R)
    (resolventDisk : closedBall μ R \ {μ} ⊆ resolventSet ℂ a)
    (pole : Tendsto (fun z : ℂ => (z - μ) • resolvent a z) (𝓝[≠] μ) (𝓝 p)) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∮ z in C(μ, R), resolvent a z) = p := by
  let f := fun z : ℂ => (z - μ) • resolvent a z
  have continuous : ContinuousOn f (closedBall μ R \ {μ}) := by
    intro z hz
    have hc : ContinuousAt (fun w : ℂ => (w - μ) • resolvent a w) z :=
      (continuousAt_id.sub_const μ).smul
        (spectrum.hasDerivAt_resolvent_const_left (resolventDisk hz)).continuousAt
    exact hc.continuousWithinAt
  have differentiable : ∀ z ∈ (ball μ R \ {μ}) \ (∅ : Set ℂ), DifferentiableAt ℂ f z := by
    intro z hz
    exact (differentiableAt_id.sub_const μ).smul
      (spectrum.hasDerivAt_resolvent_const_left
        (resolventDisk ⟨ball_subset_closedBall hz.1.1, hz.1.2⟩)).differentiableAt
  have cauchy := Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
    hR countable_empty continuous differentiable pole
  change (∮ z in C(μ, R), (z - μ)⁻¹ • (z - μ) • resolvent a z) =
    (2 * Real.pi * Complex.I : ℂ) • p at cauchy
  rw [circleIntegral.integral_sub_inv_smul_sub_smul] at cauchy
  rw [cauchy, inv_smul_smul₀]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

/-- Every sufficiently small circle around the selected eigenvalue yields the
actual projector. The circle and its spectral separation are constructed. -/
theorem exists_circle (a p : A) (μ : ℂ) (hμ : μ ≠ 0) (hp : p * p = p)
    (hap : a * p = μ • p) (hpa : p * a = μ • p)
    (hcomplement : μ ∈ resolventSet ℂ (a - μ • p)) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ R : ℝ, 0 < R → R ≤ radius →
      (closedBall μ R \ {μ} ⊆ resolventSet ℂ a) ∧
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∮ z in C(μ, R), resolvent a z) = p := by
  have near : resolventSet ℂ (a - μ • p) ∩ ({0} : Set ℂ)ᶜ ∈ 𝓝 μ :=
    inter_mem ((spectrum.isOpen_resolventSet _).mem_nhds hcomplement)
      (isOpen_compl_singleton.mem_nhds hμ)
  obtain ⟨radius, hpositive, hball⟩ := Metric.mem_nhds_iff.mp near
  refine ⟨radius / 2, by positivity, fun R hR hsmall => ?_⟩
  have subset : closedBall μ R \ {μ} ⊆ resolventSet ℂ a := by
    intro z hz
    have hzr : dist z μ < radius := (hz.1.trans hsmall).trans_lt (by linarith)
    have hzdata := hball hzr
    exact (formula a p μ z hp hap hpa hzdata.2 hz.2 hzdata.1).1
  exact ⟨subset, circle_integral_eq a p μ R hR subset (residue a p μ hμ hp hap hpa hcomplement)⟩

end LeanShared.RankOneResolvent
