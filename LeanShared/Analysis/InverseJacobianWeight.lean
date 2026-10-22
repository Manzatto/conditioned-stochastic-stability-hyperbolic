module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The literal inverse Jacobian weight

The spatial derivative and its determinant are taken from the actual map.
Continuity, strict positivity, and compact uniform bounds are conclusions.
For manifold applications these are coordinate results; the identification
with the manifold volume Jacobian remains a separate classical bridge.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace LeanShared.InverseJacobianWeight

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace Ω]

def spatialDerivative (F : E × Ω → E) (p : E × Ω) : E →L[ℝ] E :=
  fderiv ℝ (fun x => F (x, p.2)) p.1

/-- `G (y,ω)` is the inverse image of `y`; no inverse relation is built into
this definition or silently used in the continuity proof. -/
def weight (F G : E × Ω → E) (φ : E → ℝ) (p : E × Ω) : ℝ :=
  Real.exp (φ (G p)) / |(spatialDerivative F (G p, p.2)).det|

omit [TopologicalSpace Ω] in
/-- An actual invertible spatial derivative has nonzero determinant. -/
theorem det_ne_zero_of_hasFDerivAt (F : E × Ω → E) (x : E) (ω : Ω)
    (A : E ≃L[ℝ] E) (hF : HasFDerivAt (fun z => F (z, ω)) (A : E →L[ℝ] E) x) :
    (spatialDerivative F (x, ω)).det ≠ 0 := by
  unfold spatialDerivative
  rw [hF.fderiv]
  exact A.toLinearEquiv.isUnit_det'.ne_zero

omit [TopologicalSpace Ω] in
theorem weight_pos (F G : E × Ω → E) (φ : E → ℝ) (p : E × Ω)
    (hdet : (spatialDerivative F (G p, p.2)).det ≠ 0) : 0 < weight F G φ p :=
  div_pos (Real.exp_pos _) (abs_pos.mpr hdet)

/-- Continuity on the relevant region suffices even if the inverse map is
only represented in a local coordinate chart. -/
theorem continuousOn_weight (F G : E × Ω → E) (φ : E → ℝ) (S : Set (E × Ω))
    (hG : ContinuousOn G S) (hφ : Continuous φ) (hD : Continuous (spatialDerivative F))
    (hdet : ∀ p ∈ S, (spatialDerivative F (G p, p.2)).det ≠ 0) :
    ContinuousOn (weight F G φ) S := by
  have hn : ContinuousOn (fun p => Real.exp (φ (G p))) S :=
    (Real.continuous_exp.comp hφ).comp_continuousOn hG
  have hJ : ContinuousOn (fun p => spatialDerivative F (G p, p.2)) S :=
    hD.comp_continuousOn (hG.prodMk continuousOn_snd)
  have hd : ContinuousOn (fun p => |(spatialDerivative F (G p, p.2)).det|) S :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn hJ).abs
  exact hn.div hd (fun p hp => abs_ne_zero.mpr (hdet p hp))

theorem continuous_weight (F G : E × Ω → E) (φ : E → ℝ)
    (hG : Continuous G) (hφ : Continuous φ) (hD : Continuous (spatialDerivative F))
    (hdet : ∀ p, (spatialDerivative F (G p, p.2)).det ≠ 0) :
    Continuous (weight F G φ) :=
  continuousOn_univ.mp
    (continuousOn_weight F G φ univ hG.continuousOn hφ hD (fun p _ => hdet p))

/-- The actual positive Jacobian weight has both a strictly positive lower
bound and a finite nonnegative upper bound on every compact region. -/
theorem exists_uniform_bounds (F G : E × Ω → E) (φ : E → ℝ) (S : Set (E × Ω))
    (hS : IsCompact S) (hG : ContinuousOn G S) (hφ : Continuous φ)
    (hD : Continuous (spatialDerivative F))
    (hdet : ∀ p ∈ S, (spatialDerivative F (G p, p.2)).det ≠ 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ p ∈ S, a ≤ weight F G φ p ∧ weight F G φ p ≤ b := by
  have hc := continuousOn_weight F G φ S hG hφ hD hdet
  obtain ⟨a, ha, hamin⟩ := hS.exists_forall_le' hc (fun p hp => weight_pos F G φ p (hdet p hp))
  obtain ⟨b, hb⟩ := hS.bddAbove_image hc
  refine ⟨a, max b 0, ha, le_max_right _ _, ?_⟩
  intro p hp
  exact ⟨hamin p hp, (hb (mem_image_of_mem _ hp)).trans (le_max_left _ _)⟩

/-- The spatial derivative field is derived from an actual jointly `C¹`
family, rather than supplied as an unrelated continuous field. -/
theorem continuous_spatialDerivative_of_contDiff
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : E × P → E) (hF : ContDiff ℝ 1 F) : Continuous (spatialDerivative F) := by
  have hformula : spatialDerivative F = fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E P) := by
    funext p
    exact ((hF.differentiable (by simp) p).hasFDerivAt.comp p.1
      ((hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1))).fderiv
  rw [hformula]
  exact (hF.continuous_fderiv (by simp)).clm_comp continuous_const

/-- End-to-end coordinate producer: joint `C¹` regularity and actual
invertible spatial derivatives imply all continuity and weight bounds.
The compact region may in particular be a compact state set times a
compact noise set. -/
theorem continuous_positive_bounded_weight_of_contDiff
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F G : E × P → E) (φ : E → ℝ) (S : Set (E × P)) (hS : IsCompact S)
    (hF : ContDiff ℝ 1 F) (hG : Continuous G) (hφ : Continuous φ)
    (hspatial : ∀ x ω, ∃ A : E ≃L[ℝ] E,
      HasFDerivAt (fun z => F (z, ω)) (A : E →L[ℝ] E) x) :
    Continuous (weight F G φ) ∧ (∀ p, 0 < weight F G φ p) ∧
      ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ p ∈ S, a ≤ weight F G φ p ∧ weight F G φ p ≤ b := by
  have hD := continuous_spatialDerivative_of_contDiff F hF
  have hdet : ∀ p : E × P, (spatialDerivative F (G p, p.2)).det ≠ 0 := by
    intro p
    obtain ⟨A, hA⟩ := hspatial (G p) p.2
    exact det_ne_zero_of_hasFDerivAt F (G p) p.2 A hA
  exact ⟨continuous_weight F G φ hG hφ hD hdet,
    (fun p => weight_pos F G φ p (hdet p)),
    exists_uniform_bounds F G φ S hS hG.continuousOn hφ hD (fun p _ => hdet p)⟩

/-- The continuous literal weight is measurable in the actual product
Borel structure. Finite-dimensional real state spaces supply the required
second-countable topology. -/
theorem measurable_weight [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology E]
    (F G : E × Ω → E) (φ : E → ℝ)
    (hG : Continuous G) (hφ : Continuous φ) (hD : Continuous (spatialDerivative F))
    (hdet : ∀ p, (spatialDerivative F (G p, p.2)).det ≠ 0) :
    Measurable (weight F G φ) :=
  (continuous_weight F G φ hG hφ hD hdet).measurable

end LeanShared.InverseJacobianWeight
