module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Compact operators descending through dual restriction

Hahn--Banach extends each functional without increasing its norm. The choices
need not form a linear extension map. A full-dual operator invariant under
restriction nevertheless descends linearly and compactly to the subspace dual.
-/

@[expose] public noncomputable section

open Set Metric

namespace LeanShared.DualRestrictionCompactness

variable {B F : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (V : Submodule ℂ B)

/-- An individual norm-preserving Hahn--Banach extension; no linearity of
this choice function is asserted. -/
def extension (f : V →L[ℂ] ℂ) : B →L[ℂ] ℂ := (exists_extension_norm_eq V f).choose

theorem extension_apply (f : V →L[ℂ] ℂ) (v : V) : extension V f v = f v :=
  (exists_extension_norm_eq V f).choose_spec.1 v

theorem norm_extension (f : V →L[ℂ] ℂ) : ‖extension V f‖ = ‖f‖ :=
  (exists_extension_norm_eq V f).choose_spec.2

variable (T : (B →L[ℂ] ℂ) →L[ℂ] F)
  (hcompat : ∀ f g : B →L[ℂ] ℂ, (∀ v : V, f v = g v) → T f = T g)

/-- Restriction compatibility proves the descended operator is linear even
though norm-preserving extension choices generally are not linear. -/
def descendLinearMap : (V →L[ℂ] ℂ) →ₗ[ℂ] F where
  toFun f := T (extension V f)
  map_add' f g := by
    have he : T (extension V (f + g)) = T (extension V f + extension V g) := by
      apply hcompat
      intro v
      rw [extension_apply]
      change f v + g v = extension V f v + extension V g v
      rw [extension_apply, extension_apply]
    exact he.trans (T.map_add _ _)
  map_smul' c f := by
    have he : T (extension V (c • f)) = T (c • extension V f) := by
      apply hcompat
      intro v
      rw [extension_apply]
      change c • f v = c • extension V f v
      rw [extension_apply]
    exact he.trans (T.map_smul c _)

theorem descendLinearMap_bound (f : V →L[ℂ] ℂ) :
    ‖descendLinearMap V T hcompat f‖ ≤ ‖T‖ * ‖f‖ := by
  change ‖T (extension V f)‖ ≤ _
  simpa only [norm_extension] using T.le_opNorm (extension V f)

/-- The genuinely constructed bounded linear map on the subspace dual. -/
def descend : (V →L[ℂ] ℂ) →L[ℂ] F :=
  LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := V →L[ℂ] ℂ) (F := F)
    (descendLinearMap V T hcompat) ‖T‖
    (descendLinearMap_bound V T hcompat)

theorem descend_apply (f : V →L[ℂ] ℂ) : descend V T hcompat f = T (extension V f) := rfl

/-- Any extension gives the same output, so the descended value is independent
of the chosen Hahn--Banach extension. -/
theorem descend_eq_of_extension (f : V →L[ℂ] ℂ) (g : B →L[ℂ] ℂ)
    (hg : ∀ v : V, g v = f v) : descend V T hcompat f = T g := by
  apply hcompat
  intro v
  rw [extension_apply, hg v]

/-- Compactness transfers via norm-preserving extensions of bounded balls,
without assuming a bounded linear right inverse to restriction. -/
theorem descend_isCompact (hT : IsCompactOperator T) : IsCompactOperator (descend V T hcompat) := by
  obtain ⟨K, hK, hsub⟩ := hT.image_closedBall_subset_compact
    (f := T.toLinearMap) 1
  apply (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).mpr
  refine ⟨closedBall (0 : V →L[ℂ] ℂ) 1,
    closedBall_mem_nhds (0 : V →L[ℂ] ℂ) zero_lt_one, K, hK, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  apply hsub
  refine ⟨extension V f, ?_, rfl⟩
  have hfn : ‖f‖ ≤ 1 := by
    have hh : dist f 0 ≤ 1 := Metric.mem_closedBall.mp hf
    rwa [dist_zero_right (E := V →L[ℂ] ℂ) f] at hh
  apply Metric.mem_closedBall.mpr
  rwa [dist_zero_right (E := B →L[ℂ] ℂ) (extension V f), norm_extension]

end LeanShared.DualRestrictionCompactness
