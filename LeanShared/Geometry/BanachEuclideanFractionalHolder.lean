module
public import LeanShared.Geometry.EuclideanFractionalHolder
public import LeanShared.Analysis.BanachCompactSupportedLocalHolder

/-! Actual compactly supported fractional functions with arbitrary Banach
values have a produced global lower-order Hölder bound. -/
public noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace LeanShared.FractionalManifoldRegularity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem global_holder_of_regular_banach [FiniteDimensional ℝ E]
    (f : E →ᵇ F) (compact : HasCompactSupport f) {a : ℝ}
    (ha : 0<a) (ha1 : a<1) (hf : Regular (E:=E) (F:=F) a (fun x=>f x)) :
    ∃ C : ℝ, 0≤C ∧ ∀x y,‖f x-f y‖≤C*‖x-y‖^a := by
  simpa only [dist_eq_norm] using BanachCompactSupportedLocalHolder.exists_bound f compact ha ha1.le
    (fun x => by simpa only [dist_eq_norm] using local_holder_of_regular ha ha1 hf x)
end LeanShared.FractionalManifoldRegularity
