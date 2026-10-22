module
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! An actual affine embedding with a continuous linear left inverse carries
an explicit smooth chart, and its actual inclusion differential is injective. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.AffineImmersionChart
variable {U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] def carrier (i : U →L[ℝ] E) (a : E) : Set E := range (fun u => i u+a)

@[expose] def parametrization (i : U →L[ℝ] E) (r : E →L[ℝ] U)
    (left : ∀ u, r (i u)=u) (a : E) : U ≃ₜ carrier i a where
  toFun u := ⟨i u+a,⟨u,rfl⟩⟩
  invFun x := r (x.val-a)
  left_inv u := by simp only [add_sub_cancel_right,left]
  right_inv x := by
    obtain ⟨u,hu⟩ := x.property
    apply Subtype.ext
    change i (r (x.val-a))+a=x.val
    rw [← hu,add_sub_cancel_right,left]
  continuous_toFun := (i.continuous.add continuous_const).subtype_mk _
  continuous_invFun := r.continuous.comp (continuous_subtype_val.sub continuous_const)

theorem exists_chart (i : U →L[ℝ] E) (r : E →L[ℝ] U)
    (left : ∀ u, r (i u)=u) (a : E) :
    ∃ atlas : ChartedSpace U (carrier i a), letI := atlas
      IsManifold (𝓘(ℝ,U)) 1 (carrier i a) ∧
      ContMDiff (𝓘(ℝ,U)) (𝓘(ℝ,E)) 1 (Subtype.val : carrier i a → E) ∧
      ∀ x : carrier i a, Function.Injective
        (mfderiv (𝓘(ℝ,U)) (𝓘(ℝ,E)) (Subtype.val : carrier i a → E) x) := by
  let e := parametrization i r left a
  let _ : Nonempty (carrier i a) := ⟨e 0⟩
  let h := e.symm.isOpenEmbedding
  let atlas := h.singletonChartedSpace
  let _ : ChartedSpace U (carrier i a) := atlas
  let _ : IsManifold (𝓘(ℝ,U)) 1 (carrier i a) := h.isManifold_singleton
  have gSmooth : ContMDiff (𝓘(ℝ,U)) (𝓘(ℝ,U)) 1 e.symm := contMDiff_isOpenEmbedding h
  have eSmooth : ContMDiff (𝓘(ℝ,U)) (𝓘(ℝ,U)) 1 e := by
    apply ContMDiff.of_comp_isOpenEmbedding h
    have comp : e.symm ∘ e = (id : U → U) := by
      funext u
      exact e.symm_apply_apply u
    rw [comp]
    exact contMDiff_id
  let d : U ≃ₘ^1⟮𝓘(ℝ,U),𝓘(ℝ,U)⟯ carrier i a :=
    { e.toEquiv with contMDiff_toFun := eSmooth,contMDiff_invFun := gSmooth }
  have includeSmooth : ContMDiff (𝓘(ℝ,U)) (𝓘(ℝ,E)) 1
      (Subtype.val : carrier i a → E) := by
    have affine : ContMDiff (𝓘(ℝ,U)) (𝓘(ℝ,E)) 1 (fun u => i u+a) :=
      i.contMDiff.add contMDiff_const
    convert affine.comp gSmooth using 1
    funext x
    exact (congrArg Subtype.val (e.apply_symm_apply x)).symm
  refine ⟨atlas,inferInstance,includeSmooth,fun x => ?_⟩
  have retract : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,U)) 1 (fun y => r (y-a)) :=
    r.contMDiff.comp (contDiff_id.sub contDiff_const).contMDiff
  have chain := mfderiv_comp x (retract.mdifferentiable (by decide) x.val)
    (includeSmooth.mdifferentiable (by decide) x)
  have idG : (fun y => r (y-a)) ∘ (Subtype.val : carrier i a → E) = e.symm := rfl
  rw [idG] at chain
  have injectiveG : Function.Injective
      (mfderiv (𝓘(ℝ,U)) (𝓘(ℝ,U)) e.symm x) := by
    change Function.Injective (mfderiv (𝓘(ℝ,U)) (𝓘(ℝ,U)) d.symm x)
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe d.symm (by decide)]
    exact (d.symm.mfderivToContinuousLinearEquiv (by decide) x).injective
  intro v w hvw
  apply injectiveG
  rw [chain]
  exact congrArg (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,U)) (fun y => r (y-a)) x.val) hvw
end LeanShared.AffineImmersionChart
