module

public import LeanShared.Dynamics.ToralCatMapDerivative
public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Analysis.IntertwinedProjectionSubspaces

/-! A literal full-core uniformly hyperbolic tangent certificate for the
concrete cat map. The splitting and contraction are transported through
the actual quotient differential and the constructed continuous flat
Riemannian metric, and use the actual manifold derivatives of iterates. -/

set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set IsManifold Bundle Function
open scoped Manifold ContDiff Bundle Topology
namespace LeanShared.ToralCatMap

def tangentStable (x : Torus) : Submodule ℝ (TangentSpace (𝓘(ℝ, HilbertModel)) x) :=
  stable.map (realTangentFrame x).toLinearMap

def tangentUnstable (x : Torus) : Submodule ℝ (TangentSpace (𝓘(ℝ, HilbertModel)) x) :=
  unstable.map (realTangentFrame x).toLinearMap

def tangentProjection (x : Torus) : TangentSpace (𝓘(ℝ, HilbertModel)) x →L[ℝ]
    TangentSpace (𝓘(ℝ, HilbertModel)) x :=
  (realTangentFrame x).toContinuousLinearMap.comp
    (projection.comp (realTangentFrame x).symm.toContinuousLinearMap)

theorem tangentProjection_apply (x : Torus) (v : TangentSpace (𝓘(ℝ, HilbertModel)) x) :
    tangentProjection x v = realTangentFrame x (projection ((realTangentFrame x).symm v)) := rfl

theorem tangentProjection_range (x : Torus) : (tangentProjection x).range = tangentStable x := by
  have equal := IntertwinedProjectionSubspaces.range_map projection (tangentProjection x) (realTangentFrame x)
    (fun v => by simp only [tangentProjection_apply, ContinuousLinearEquiv.symm_apply_apply])
  rw [← equal, projection_range]
  rfl

theorem tangentProjection_kernel (x : Torus) : (tangentProjection x).ker = tangentUnstable x := by
  have equal := IntertwinedProjectionSubspaces.kernel_map projection (tangentProjection x) (realTangentFrame x)
    (fun v => by simp only [tangentProjection_apply, ContinuousLinearEquiv.symm_apply_apply])
  rw [← equal, projection_kernel]
  rfl

theorem tangentProjection_idempotent (x : Torus) :
    (tangentProjection x).comp (tangentProjection x) = tangentProjection x := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, tangentProjection_apply, ContinuousLinearEquiv.symm_apply_apply]
  exact congrArg (realTangentFrame x) (congrArg (fun P => P ((realTangentFrame x).symm v)) projection_idempotent)

theorem tangent_complementary (x : Torus) : IsCompl (tangentStable x) (tangentUnstable x) := by
  rw [← tangentProjection_range, ← tangentProjection_kernel]
  apply LinearMap.IsIdempotentElem.isCompl
  ext v
  exact congrArg (fun P => P v) (tangentProjection_idempotent x)

theorem continuous_realFrame :
    Continuous (fun p : Torus × (ℝ × ℝ) =>
      (⟨p.1, realTangentFrame p.1 p.2⟩ : TangentBundle (𝓘(ℝ, HilbertModel)) Torus)) :=
  continuous_frame.comp (continuous_fst.prodMk (liftHilbertEquivalence.continuous.comp continuous_snd))

theorem continuous_realCoframe :
    Continuous (fun p : TangentBundle (𝓘(ℝ, HilbertModel)) Torus => (realTangentFrame p.1).symm p.2) :=
  liftHilbertEquivalence.symm.continuous.comp continuous_coframe

theorem continuous_tangentProjection :
    Continuous (fun p : TangentBundle (𝓘(ℝ, HilbertModel)) Torus =>
      (⟨p.1, tangentProjection p.1 p.2⟩ : TangentBundle (𝓘(ℝ, HilbertModel)) Torus)) :=
  continuous_realFrame.comp ((FiberBundle.continuous_proj HilbertModel _).prodMk
    (projection.continuous.comp continuous_realCoframe))

theorem tangentStable_invariant (x : Torus) :
    (tangentStable x).map (mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) homeomorph x).toLinearMap =
      tangentStable (homeomorph x) := by
  have intertwines : (mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) homeomorph x).toLinearMap.comp
      (realTangentFrame x).toLinearMap = (realTangentFrame (homeomorph x)).toLinearMap.comp linear := by
    apply LinearMap.ext
    intro v
    exact derivative_map_realFrame x v
  unfold tangentStable
  rw [← Submodule.map_comp, intertwines, Submodule.map_comp, stable_invariant]

theorem tangentUnstable_invariant (x : Torus) :
    (tangentUnstable x).map (mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) homeomorph x).toLinearMap =
      tangentUnstable (homeomorph x) := by
  have intertwines : (mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) homeomorph x).toLinearMap.comp
      (realTangentFrame x).toLinearMap = (realTangentFrame (homeomorph x)).toLinearMap.comp linear := by
    apply LinearMap.ext
    intro v
    exact derivative_map_realFrame x v
  unfold tangentUnstable
  rw [← Submodule.map_comp, intertwines, Submodule.map_comp, unstable_invariant]

theorem norm_realTangentFrame (x : Torus) (v : ℝ × ℝ) :
    ‖realTangentFrame x v‖ = ‖liftHilbertEquivalence v‖ := norm_tangentFrame x _

theorem stable_derivative_bound (n : ℕ) (x : Torus) (v : TangentSpace (𝓘(ℝ, HilbertModel)) x)
    (member : v ∈ tangentStable x) :
    ‖mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) ((homeomorph : Torus → Torus)^[n]) x v‖ ≤
      contracting ^ n * ‖v‖ := by
  obtain ⟨w, hw, rfl⟩ := member
  change ‖mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) ((homeomorph : Torus → Torus)^[n]) x
    (realTangentFrame x w)‖ ≤ contracting ^ n * ‖realTangentFrame x w‖
  rw [derivative_iterate_realFrame, iterate_stable n w hw, norm_realTangentFrame,
    liftHilbertEquivalence.map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg contracting_pos.le n), norm_realTangentFrame]

theorem unstable_derivative_bound (n : ℕ) (x : Torus) (v : TangentSpace (𝓘(ℝ, HilbertModel)) x)
    (member : v ∈ tangentUnstable x) :
    ‖mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) ((homeomorph.symm : Torus → Torus)^[n]) x v‖ ≤
      contracting ^ n * ‖v‖ := by
  obtain ⟨w, hw, rfl⟩ := member
  change ‖mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) ((homeomorph.symm : Torus → Torus)^[n]) x
    (realTangentFrame x w)‖ ≤ contracting ^ n * ‖realTangentFrame x w‖
  rw [derivative_inverse_iterate_realFrame, inverse_iterate_unstable n w hw, norm_realTangentFrame,
    liftHilbertEquivalence.map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg contracting_pos.le n), norm_realTangentFrame]

def hyperbolic : HyperbolicBasicSet.HyperbolicData (E := HilbertModel) homeomorph univ where
  compact := isCompact_univ
  invariant := by simp
  stable := tangentStable
  unstable := tangentUnstable
  complementary x _ := tangent_complementary x
  projection := tangentProjection
  projection_range x _ := tangentProjection_range x
  projection_kernel x _ := tangentProjection_kernel x
  projection_idempotent x _ := tangentProjection_idempotent x
  continuous_splitting := continuous_tangentProjection.continuousOn
  stable_invariant x _ := tangentStable_invariant x
  unstable_invariant x _ := tangentUnstable_invariant x
  constant := 1
  contraction := contracting
  constant_pos := zero_lt_one
  contraction_pos := contracting_pos
  contraction_lt_one := contracting_lt_one
  stable_bound n x _ v hv := by simpa only [one_mul] using stable_derivative_bound n x v hv
  unstable_bound n x _ v hv := by simpa only [one_mul] using unstable_derivative_bound n x v hv

theorem tangentStable_finrank (x : Torus) : Module.finrank ℝ (tangentStable x) = 1 := by
  rw [tangentStable, LinearEquiv.finrank_map_eq, stable_finrank]

theorem tangentUnstable_finrank (x : Torus) : Module.finrank ℝ (tangentUnstable x) = 1 := by
  rw [tangentUnstable, LinearEquiv.finrank_map_eq, unstable_finrank]

def basicData : HyperbolicBasicSet.BasicData (E := HilbertModel) homeomorph univ univ where
  hyperbolic := hyperbolic
  nonempty := univ_nonempty
  open_neighborhood := isOpen_univ
  subset_neighborhood := subset_rfl
  isolated := by ext x; simp [LeanShared.isolatedCore, LeanShared.forwardTrapped]
  dense_orbit := dense_orbit

end LeanShared.ToralCatMap
