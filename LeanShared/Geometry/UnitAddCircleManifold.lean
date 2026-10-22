module

public import LeanShared.Geometry.HomeomorphTransportManifold
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! A genuine smooth manifold and additive Lie-group structure on the
actual unit additive circle. They are transported through mathlib's
explicit homeomorphism to the analytic complex unit circle. The ordinary
real quotient projection is smooth through the actual circle exponential. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.UnitAddCircleManifold

abbrev Model := EuclideanSpace ℝ (Fin 1)

def equivalence : UnitAddCircle ≃ₜ Circle :=
  AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero

instance chartedSpace : ChartedSpace Model UnitAddCircle :=
  HomeomorphTransportManifold.charts (E := Model) equivalence

instance manifold : IsManifold (𝓘(ℝ, Model)) ∞ UnitAddCircle :=
  HomeomorphTransportManifold.manifold (E := Model) equivalence

def diffeomorph : UnitAddCircle ≃ₘ⟮𝓘(ℝ, Model), 𝓘(ℝ, Model)⟯ Circle :=
  HomeomorphTransportManifold.diffeomorph (E := Model) equivalence

theorem smooth_equivalence : ContMDiff (𝓘(ℝ, Model)) (𝓘(ℝ, Model)) ∞ equivalence :=
  HomeomorphTransportManifold.smooth (E := Model) equivalence

theorem smooth_equivalence_symm : ContMDiff (𝓘(ℝ, Model)) (𝓘(ℝ, Model)) ∞ equivalence.symm :=
  HomeomorphTransportManifold.smooth_symm (E := Model) equivalence

theorem equivalence_coe (x : ℝ) : equivalence (x : UnitAddCircle) = Circle.exp (2 * Real.pi * x) := by
  simp only [equivalence, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, div_one]

theorem smooth_projection :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) ∞ (fun x : ℝ => (x : UnitAddCircle)) := by
  have identity : (fun x : ℝ => equivalence.symm (Circle.exp (2 * Real.pi * x))) =
      (fun x : ℝ => (x : UnitAddCircle)) := by
    funext x
    apply equivalence.injective
    rw [Homeomorph.apply_symm_apply, equivalence_coe]
  rw [← identity]
  have scale : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun x : ℝ => 2 * Real.pi * x) :=
    (contDiff_const.mul contDiff_id).contMDiff
  exact smooth_equivalence_symm.comp
    (contMDiff_circleExp.comp scale)

theorem smooth_add : ContMDiff ((𝓘(ℝ, Model)).prod (𝓘(ℝ, Model))) (𝓘(ℝ, Model)) ∞
    (fun z : UnitAddCircle × UnitAddCircle => z.1 + z.2) := by
  have identity : (fun z : UnitAddCircle × UnitAddCircle =>
      equivalence.symm (equivalence z.1 * equivalence z.2)) = (fun z => z.1 + z.2) := by
    funext z
    apply equivalence.injective
    rw [Homeomorph.apply_symm_apply]
    simpa only [equivalence, AddCircle.homeomorphCircle_apply] using
      (AddCircle.toCircle_add z.1 z.2).symm
  rw [← identity]
  exact smooth_equivalence_symm.comp
    ((smooth_equivalence.comp contMDiff_fst).mul (smooth_equivalence.comp contMDiff_snd))

theorem smooth_neg : ContMDiff (𝓘(ℝ, Model)) (𝓘(ℝ, Model)) ∞
    (fun x : UnitAddCircle => -x) := by
  have identity : (fun x : UnitAddCircle => equivalence.symm (equivalence x)⁻¹) =
      (fun x => -x) := by
    funext x
    apply equivalence.injective
    rw [Homeomorph.apply_symm_apply]
    simpa only [equivalence, AddCircle.homeomorphCircle_apply] using
      (AddCircle.toCircle_neg x).symm
  rw [← identity]
  exact smooth_equivalence_symm.comp smooth_equivalence.inv

instance lieAddGroup : LieAddGroup (𝓘(ℝ, Model)) ∞ UnitAddCircle where
  contMDiff_add := smooth_add
  contMDiff_neg := smooth_neg

end LeanShared.UnitAddCircleManifold
