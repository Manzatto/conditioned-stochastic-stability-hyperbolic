module

public import LeanShared.Analysis.SchwartzJetSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Actual smooth manifold chart localization

A compactly supported smooth cutoff inside a genuine smooth chart constructs
the localized Schwartz core map. Zero extension across the chart boundary is
proved smooth because the cutoff support stays inside the chart. Thus the
finite-chart compactness consumer needs no supplied localization linear map.
The existence of an adapted atlas/partition and geometric area identification
are separate classical inputs.
-/

@[expose] public noncomputable section

open Set IsManifold
open scoped Manifold ContDiff SchwartzMap

namespace LeanShared.ChartLocalization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (e : OpenPartialHomeomorph M E) (θ : M → ℂ)

/-- Literal coordinate formula, zero outside the chart target. -/
def coordinate (f : M → ℂ) (y : E) : ℂ := by
  classical
  exact if y ∈ e.target then θ (e.symm y) * f (e.symm y) else 0

/-- Fixed compact localization support, determined only by the cutoff. -/
def localSupport : Set E := e '' tsupport θ

variable (hsupp : tsupport θ ⊆ e.source)

include hsupp in
omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem localSupport_subset_target : localSupport e θ ⊆ e.target := by
  rintro _ ⟨x, hx, rfl⟩
  exact e.map_source (hsupp hx)

include hsupp in
omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem localSupport_isCompact (hcompact : HasCompactSupport θ) :
    IsCompact (localSupport e θ) :=
  hcompact.image_of_continuousOn (e.continuousOn.mono hsupp)

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem coordinate_zero_outside (f : M → ℂ) (y : E) (hy : y ∉ localSupport e θ) :
    coordinate e θ f y = 0 := by
  by_cases hyt : y ∈ e.target
  · have hθ : θ (e.symm y) = 0 := by
      by_contra hn
      apply hy
      exact ⟨e.symm y, subset_tsupport θ (show e.symm y ∈ Function.support θ from hn),
        e.right_inv hyt⟩
    simp only [coordinate, ite_eq_left hyt, hθ, zero_mul]
  · simp only [coordinate, ite_eq_right hyt]

include hsupp in
omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem coordinate_hasCompactSupport (hcompact : HasCompactSupport θ) (f : M → ℂ) :
    HasCompactSupport (coordinate e θ f) :=
  HasCompactSupport.intro (localSupport_isCompact e θ hsupp hcompact)
    (fun y hy => coordinate_zero_outside e θ f y hy)

variable (he : e ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  (hθ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ θ)

include hsupp he hθ in
theorem coordinate_contDiff (hcompact : HasCompactSupport θ)
    (f : M → ℂ) (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ f) :
    ContDiff ℝ ∞ (coordinate e θ f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ e.target
  · have hc : ContDiffAt ℝ ∞ (fun y => θ (e.symm y) * f (e.symm y)) x :=
      (((hθ (e.symm x)).comp x
        (contMDiffAt_symm_of_mem_maximalAtlas he hx)).contDiffAt).mul
        (((hf (e.symm x)).comp x
          (contMDiffAt_symm_of_mem_maximalAtlas he hx)).contDiffAt)
    apply hc.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    exact ite_eq_left hy
  · have hxc : x ∉ localSupport e θ := fun hc => hx (localSupport_subset_target e θ hsupp hc)
    have hc : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℂ)) x := contDiffAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [(localSupport_isCompact e θ hsupp hcompact).isClosed.isOpen_compl.mem_nhds hxc]
      with y hy
    exact coordinate_zero_outside e θ f y hy

variable {Core : Type*} [AddCommGroup Core] [Module ℂ Core]
  (functions : Core →ₗ[ℂ] (M → ℂ))
  (smooth : ∀ f : Core, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (functions f))
  (hcompact : HasCompactSupport θ)

/-- The actual cutoff/chart localization into the supported Schwartz core. -/
def linearMap : Core →ₗ[ℂ] SchwartzJetSpace.supportedCore (localSupport e θ) where
  toFun f := ⟨(coordinate_hasCompactSupport e θ hsupp hcompact (functions f)).toSchwartzMap
    (coordinate_contDiff e θ hsupp he hθ hcompact (functions f) (smooth f)),
    coordinate_zero_outside e θ (functions f)⟩
  map_add' f g := by
    apply Subtype.ext
    ext y
    change coordinate e θ (functions (f + g)) y =
      coordinate e θ (functions f) y + coordinate e θ (functions g) y
    by_cases hy : y ∈ e.target
    · simp only [coordinate, ite_eq_left hy, map_add, Pi.add_apply, mul_add]
    · simp only [coordinate, ite_eq_right hy, zero_add]
  map_smul' c f := by
    apply Subtype.ext
    ext y
    change coordinate e θ (functions (c • f)) y = c • coordinate e θ (functions f) y
    by_cases hy : y ∈ e.target
    · simp only [coordinate, ite_eq_left hy, map_smul, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [coordinate, ite_eq_right hy, smul_zero]

@[simp]
theorem linearMap_apply (f : Core) (y : E) :
    (linearMap e θ hsupp he hθ functions smooth hcompact f).val y = coordinate e θ (functions f) y := rfl

omit [NormedSpace ℝ E] [ChartedSpace E M] in
/-- On the original chart this is precisely the manuscript localization. -/
theorem coordinate_chart (f : M → ℂ) (x : M) (hx : x ∈ e.source) :
    coordinate e θ f (e x) = θ x * f x := by
  simp only [coordinate, ite_eq_left (e.map_source hx), e.left_inv hx]

end LeanShared.ChartLocalization
