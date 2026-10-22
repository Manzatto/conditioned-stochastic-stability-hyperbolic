module

public import LeanShared.Analysis.RankOneResolvent
public import LeanShared.Analysis.SimpleSquareCompactProjection
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The constructed invariant rank-one projector is the actual residue of
the operator resolvent at its isolated eigenvalue. -/

public section
open Filter
open scoped Topology
namespace LeanShared.RankOneResolvent
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Resolvent residue at a nonzero isolated simple eigenvalue. No contour
integral or spectral projector formula is assumed. -/
theorem residue (a p : A) (μ : ℂ) (hμ : μ ≠ 0) (hp : p * p = p)
    (hap : a * p = μ • p) (hpa : p * a = μ • p)
    (hcomplement : μ ∈ resolventSet ℂ (a - μ • p)) :
    Tendsto (fun z : ℂ => (z - μ) • resolvent a z) (𝓝[≠] μ) (𝓝 p) := by
  have hcontinuity := (spectrum.hasDerivAt_resolvent_const_left hcomplement).continuousAt
  have continuous : ContinuousAt (fun z : ℂ =>
      (z - μ) • resolvent (a - μ • p) z + (μ / z) • p) μ :=
    ((continuousAt_id.sub_const μ).smul hcontinuity).add
      ((continuousAt_const.div continuousAt_id hμ).smul continuousAt_const)
  have limit : Tendsto (fun z : ℂ =>
      (z - μ) • resolvent (a - μ • p) z + (μ / z) • p) (𝓝[≠] μ) (𝓝 p) := by
    simpa only [sub_self, zero_smul, div_self hμ, one_smul, zero_add] using
      continuous.tendsto.mono_left nhdsWithin_le_nhds
  have nearComplement : ∀ᶠ z : ℂ in 𝓝[≠] μ, z ∈ resolventSet ℂ (a - μ • p) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((spectrum.isOpen_resolventSet _).mem_nhds hcomplement)
  have nearNonzero : ∀ᶠ z : ℂ in 𝓝[≠] μ, z ≠ 0 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (isOpen_compl_singleton.mem_nhds hμ)
  have nearDifferent : ∀ᶠ z : ℂ in 𝓝[≠] μ, z ≠ μ := self_mem_nhdsWithin
  apply limit.congr'
  filter_upwards [nearComplement, nearNonzero, nearDifferent] with z hz hz0 hzm
  have formula := (formula a p μ z hp hap hpa hz0 hzm hz).2
  rw [formula, smul_add, smul_smul]
  have coefficient : (z - μ) * ((z - μ)⁻¹ - z⁻¹) = μ / z := by
    field_simp [hz0, sub_ne_zero.mpr hzm]
    ring
  rw [coefficient]

end LeanShared.RankOneResolvent

namespace LeanShared.SimpleSquareCompactProjection

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The actual projector constructed from compactness and algebraic simplicity
is the limit of the rescaled resolvent at the selected eigenvalue. -/
theorem Data.residue {T : X →L[ℂ] X} {μ : ℂ} {v : X}
    (d : Data T μ v) (hμ : μ ≠ 0) :
    Tendsto (fun z : ℂ => (z - μ) • resolvent T z) (𝓝[≠] μ)
      (𝓝 (d.mean.smulRight v)) := by
  have hcomplement : μ ∈ resolventSet ℂ (T - μ • d.mean.smulRight v) := by
    by_contra h
    exact ((d.remainder_spectrum μ hμ).mp h).2 rfl
  exact RankOneResolvent.residue T (d.mean.smulRight v) μ hμ
    (by simpa only [pow_two] using d.projection_idempotent)
    d.right_action d.left_action hcomplement

end LeanShared.SimpleSquareCompactProjection
