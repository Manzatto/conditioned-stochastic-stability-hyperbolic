module

public import LeanShared.Geometry.UnitAddCircleProjectionDifferential
public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! An actual global tangent frame on the smooth additive circle, obtained
by differentiating left translations and the real quotient projection.
The frame is geometric: its definition does not identify tangent fibers
with an arbitrary coordinate-model copy. -/

@[expose] public noncomputable section
open Set IsManifold Bundle Function
open scoped Manifold ContDiff Topology
namespace LeanShared.UnitAddCircleManifold

def originDifferential : ℝ ≃L[ℝ] TangentSpace (𝓘(ℝ, Model)) (0 : UnitAddCircle) := by
  simpa only [projection, AddCircle.coe_zero] using!
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm.trans
      (projectionDifferentialEquiv 0)

theorem translationDifferential_bijective (x : UnitAddCircle) :
    Function.Bijective (mfderiv (𝓘(ℝ, Model)) (𝓘(ℝ, Model)) (fun y => x + y) 0) := by
  let e := Homeomorph.addLeft x
  have smooth : ContMDiff (𝓘(ℝ, Model)) (𝓘(ℝ, Model)) ∞ e :=
    contMDiff_const.add contMDiff_id
  have smoothInv : ContMDiff (𝓘(ℝ, Model)) (𝓘(ℝ, Model)) ∞ e.symm := by
    rw [Homeomorph.addLeft_symm]
    exact contMDiff_const.add contMDiff_id
  have h : e.toOpenPartialHomeomorph.MDifferentiable (𝓘(ℝ, Model)) (𝓘(ℝ, Model)) :=
    ⟨fun y _ => ((smooth.mdifferentiable (by simp)) y).mdifferentiableWithinAt,
     fun y _ => ((smoothInv.mdifferentiable (by simp)) y).mdifferentiableWithinAt⟩
  exact h.mfderiv_bijective (mem_univ (0 : UnitAddCircle))

def translationDifferential (x : UnitAddCircle) :
    TangentSpace (𝓘(ℝ, Model)) (0 : UnitAddCircle) ≃L[ℝ]
      TangentSpace (𝓘(ℝ, Model)) x :=
  (LinearEquiv.ofBijective (mfderiv (𝓘(ℝ, Model)) (𝓘(ℝ, Model)) (fun y => x + y) 0).toLinearMap
    (translationDifferential_bijective x)).toContinuousLinearEquiv

theorem translationDifferential_apply (x : UnitAddCircle)
    (v : TangentSpace (𝓘(ℝ, Model)) (0 : UnitAddCircle)) :
    translationDifferential x v =
      mfderiv (𝓘(ℝ, Model)) (𝓘(ℝ, Model)) (fun y => x + y) 0 v := by
  rfl

def tangentFrame (x : UnitAddCircle) : ℝ ≃L[ℝ] TangentSpace (𝓘(ℝ, Model)) x :=
  originDifferential.trans (translationDifferential x)

theorem tangentFrame_apply (x : UnitAddCircle) (r : ℝ) :
    tangentFrame x r = addInvariantVectorField (originDifferential r) x := rfl

theorem continuous_frame_section (r : ℝ) :
    Continuous (fun x : UnitAddCircle => (tangentFrame x r : TangentBundle (𝓘(ℝ, Model)) UnitAddCircle)) := by
  let : LieAddGroup (𝓘(ℝ, Model)) (minSmoothness ℝ 3) UnitAddCircle :=
    LieAddGroup.of_le (n := ∞) (by simp)
  simpa only [tangentFrame_apply] using
    (contMDiff_addInvariantVectorField (I := 𝓘(ℝ, Model)) (originDifferential r)).continuous

theorem originDifferential_apply (r : ℝ) :
    originDifferential r = mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection 0 r := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem tangentFrame_projection (t r : ℝ) :
    tangentFrame (projection t) r =
      mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection t r := by
  have commute : projection ∘ (fun u : ℝ => t + u) =
      (fun x : UnitAddCircle => projection t + x) ∘ projection := by
    funext u
    simp [projection]
  have derivative := mfderiv_congr (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model)) (x := 0) commute
  have πdiff : MDifferentiable (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection :=
    smooth_projection.mdifferentiable (by simp)
  have plusSmooth : ContDiff ℝ ∞ (fun u : ℝ => t + u) := contDiff_const.add contDiff_id
  have plus := plusSmooth.contMDiff.mdifferentiable (by simp)
  have translateSmooth : ContMDiff (𝓘(ℝ, Model)) (𝓘(ℝ, Model)) ∞
      (fun x : UnitAddCircle => projection t + x) :=
    smooth_add.comp (contMDiff_const.prodMk contMDiff_id)
  have translate := translateSmooth.mdifferentiable (by simp)
  rw [mfderiv_comp 0 (πdiff _) (plus _), mfderiv_comp 0 (translate _) (πdiff _)] at derivative
  have dplus : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun u : ℝ => t + u) 0 =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ, ℝ)) 0) := by
    rw [mfderiv_eq_fderiv]
    simpa using! (fderiv_const_add (𝕜 := ℝ) (f := @id ℝ) (x := 0) t)
  rw [dplus] at derivative
  change (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection (t + 0) : ℝ →L[ℝ] Model) = _ at derivative
  have equal := congrArg (fun A => A r) derivative
  change (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection (t + 0)) r =
    (mfderiv (𝓘(ℝ, Model)) (𝓘(ℝ, Model)) (fun x => projection t + x) (projection 0))
      ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection 0) r) at equal
  calc
    tangentFrame (projection t) r =
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection (t + 0)) r := by
      simpa only [tangentFrame, ContinuousLinearEquiv.trans_apply, translationDifferential_apply,
        originDifferential_apply, projection, AddCircle.coe_zero] using! equal.symm
    _ = (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection t) r := by
      have normalize := mfderiv_congr_point (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model))
        (f := projection) (add_zero t)
      exact congrArg (fun A => A r) normalize

def ambientDifferential (x : UnitAddCircle) : TangentSpace (𝓘(ℝ, Model)) x →L[ℝ] ℂ :=
  (NormedSpace.fromTangentSpace (𝕜 := ℝ) (ambient x)).toContinuousLinearMap.comp
    (mfderiv (𝓘(ℝ, Model)) (𝓘(ℝ, ℂ)) ambient x)

def ambientTangent (p : TangentBundle (𝓘(ℝ, Model)) UnitAddCircle) : ℂ :=
  ambientDifferential p.1 p.2

theorem continuous_ambientTangent : Continuous ambientTangent := by
  have tangent := (smooth_ambient.contMDiff_tangentMap (m := 0) (by simp)).continuous
  exact ((tangentBundleModelSpaceHomeomorph (𝓘(ℝ, ℂ))).continuous.snd).comp tangent

theorem ambientDifferential_frame (x : UnitAddCircle) (r : ℝ) :
    ambientDifferential x (tangentFrame x r) = (r : ℂ) * (ambient x * angularCoefficient) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [show (QuotientAddGroup.mk t : UnitAddCircle) = projection t from rfl,
    tangentFrame_projection]
  have chain := congrArg (fun A : ℝ →L[ℝ] ℂ => A r)
    (mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model)) (I'' := 𝓘(ℝ, ℂ)) t
      ((smooth_ambient.mdifferentiable (by simp)) (projection t))
      ((smooth_projection.mdifferentiable (by simp)) t))
  have form : ambient ∘ projection = ambientLift := funext ambient_projection
  rw [form, mfderiv_eq_fderiv, (hasDerivAt_ambientLift t).hasFDerivAt.fderiv] at chain
  simpa only [ambientDifferential, ContinuousLinearMap.comp_apply, derivativeCoefficient,
    ambient_projection, ContinuousLinearMap.toSpanSingleton_apply, Complex.real_smul] using! chain.symm

def explicitCoframe (p : TangentBundle (𝓘(ℝ, Model)) UnitAddCircle) : ℝ :=
  (ambientTangent p / (ambient p.1 * angularCoefficient)).re

theorem ambient_ne_zero (x : UnitAddCircle) : ambient x ≠ 0 := by
  exact (equivalence x).coe_ne_zero

theorem coframe_formula (x : UnitAddCircle) (v : TangentSpace (𝓘(ℝ, Model)) x) :
    (tangentFrame x).symm v = explicitCoframe ⟨x, v⟩ := by
  obtain ⟨r, rfl⟩ := (tangentFrame x).surjective v
  rw [ContinuousLinearEquiv.symm_apply_apply]
  simp only [explicitCoframe, ambientTangent, ambientDifferential_frame]
  rw [mul_div_cancel_right₀ _ (mul_ne_zero (ambient_ne_zero x) angularCoefficient_ne_zero), Complex.ofReal_re]

theorem continuous_coframe :
    Continuous (fun p : TangentBundle (𝓘(ℝ, Model)) UnitAddCircle => (tangentFrame p.1).symm p.2) := by
  simp_rw [coframe_formula]
  exact Complex.continuous_re.comp (continuous_ambientTangent.div
    ((smooth_ambient.continuous.comp (FiberBundle.continuous_proj Model (TangentSpace (𝓘(ℝ, Model))))).mul continuous_const)
    (fun p => mul_ne_zero (ambient_ne_zero p.1) angularCoefficient_ne_zero))

end LeanShared.UnitAddCircleManifold
