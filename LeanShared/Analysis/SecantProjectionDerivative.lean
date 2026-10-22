module
public import LeanShared.Analysis.SecantConeDerivative
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! The literal orthogonal projection slope of local secants bounds every
actual tangent vector, with the SAME constant. -/
public section
namespace LeanShared.SecantProjectionDerivative
open Set
open scoped Topology
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem bound {f : X → E} {A : X →L[ℝ] E} {x : X}
    (derivative : HasFDerivAt f A x) {s : Set X} (neighborhood : s ∈ 𝓝 x)
    (U : Submodule ℝ E) (L : ℝ)
    (secants : ∀ y ∈ s, ‖Uᗮ.orthogonalProjectionOnto (f y-f x)‖ ≤
      L * ‖U.orthogonalProjectionOnto (f y-f x)‖) (v : X) :
    ‖Uᗮ.orthogonalProjectionOnto (A v)‖ ≤ L * ‖U.orthogonalProjectionOnto (A v)‖ := by
  let C : Set E := {w | ‖Uᗮ.orthogonalProjectionOnto w‖ ≤ L * ‖U.orthogonalProjectionOnto w‖}
  have closed : IsClosed C := isClosed_le
    (Uᗮ.orthogonalProjectionOnto.continuous.norm)
    (continuous_const.mul U.orthogonalProjectionOnto.continuous.norm)
  have scale (a : ℝ) (_ha : 0 ≤ a) (w : E) (hw : w ∈ C) : a • w ∈ C := by
    change ‖Uᗮ.orthogonalProjectionOnto (a • w)‖ ≤ L * ‖U.orthogonalProjectionOnto (a • w)‖
    rw [map_smul, map_smul, norm_smul, norm_smul]
    have multiplied := mul_le_mul_of_nonneg_left hw (norm_nonneg a)
    exact multiplied.trans_eq (by ring)
  exact SecantConeDerivative.mem derivative neighborhood closed scale secants v

theorem range_bound {f : X → E} {A : X →L[ℝ] E} {x : X}
    (derivative : HasFDerivAt f A x) {s : Set X} (neighborhood : s ∈ 𝓝 x)
    (U : Submodule ℝ E) (L : ℝ)
    (secants : ∀ y ∈ s, ‖Uᗮ.orthogonalProjectionOnto (f y-f x)‖ ≤
      L * ‖U.orthogonalProjectionOnto (f y-f x)‖) :
    ∀ v : A.toLinearMap.range, ‖Uᗮ.orthogonalProjectionOnto (v : E)‖ ≤
      L * ‖U.orthogonalProjectionOnto (v : E)‖ := by
  rintro ⟨_, w, rfl⟩
  exact bound derivative neighborhood U L secants w
end LeanShared.SecantProjectionDerivative
