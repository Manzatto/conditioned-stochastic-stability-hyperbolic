module
public import LeanShared.Analysis.SmallAffinePerturbation
public import LeanShared.Geometry.FractionalHomeomorphInverse
public import LeanShared.Geometry.HigherFractionalAddition

/-! The actual global affine perturbation and its actual global inverse
retain the full real regularity order. This constructs the two-sided C^r
extension from a derivative bound, rather than supplying inverse regularity. -/
@[expose] public noncomputable section
open Set Function
open scoped NNReal ContDiff Manifold Topology
namespace LeanShared.SmallAffinePerturbation
open FractionalManifoldRegularity
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
theorem regular_map (A : E ≃L[ℝ] F) (b : F) {r : ℝ} {u : E → F}
    (regular : Regular (E := E) (F := F) r u) :
    Regular (E := E) (F := F) r (map A b u) := by
  change Regular (E := E) (F := F) r (fun x => A x+b+u x)
  have affine : Regular (E := E) (F := F) r (fun x => A x+b) :=
    regular_of_smooth (A.contDiff.add contDiff_const).contMDiff regular.nonnegative
  by_cases integral : r = (⌊r⌋₊ : ℝ)
  · refine ⟨regular.nonnegative, (affine.differentiable.contDiff.add regular.differentiable.contDiff).contMDiff, ?_⟩
    intro unequal
    exact (unequal integral).elim
  · have lower : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le regular.nonnegative
    have positive : 0 < r-(⌊r⌋₊ : ℝ) := by
      apply sub_pos.mpr
      exact lt_of_le_of_ne lower (Ne.symm integral)
    have small : r-(⌊r⌋₊ : ℝ) < 1 := by linarith [Nat.lt_floor_add_one r]
    have order : (r-(⌊r⌋₊ : ℝ))+(⌊r⌋₊ : ℝ) = r := sub_add_cancel _ _
    have affine' : Regular (E := E) (F := F) ((r-(⌊r⌋₊ : ℝ))+(⌊r⌋₊ : ℝ)) (fun x => A x+b) := by
      rw [order]
      exact affine
    have regular' : Regular (E := E) (F := F) ((r-(⌊r⌋₊ : ℝ))+(⌊r⌋₊ : ℝ)) u := by
      rw [order]
      exact regular
    simpa only [order] using affine'.add_noninteger positive small regular'

/-- Actual fractional regularity of the global inverse, with the original
real order preserved exactly. -/
theorem regular_inverse (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u) (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    {r : ℝ} (hr : 1 ≤ r) (regular : Regular (E := E) (F := F) r u) :
    Regular (E := F) (F := E) r (homeomorph A b lip small).symm := by
  have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hr)
  have du : Differentiable ℝ u := regular.differentiable.contDiff.differentiable
    (by exact_mod_cast (Nat.ne_of_gt order))
  apply Regular.homeomorph_inverse hr (homeomorph A b lip small) (derivativeEquiv A b lip small du)
  · intro x
    change HasFDerivAt (map A b u) _ x
    rw [derivativeEquiv_coe]
    exact ((A.differentiable.add_const b).add du x).hasFDerivAt
  · exact regular_map A b regular

/-- A C1-small actual C^r residual constructs a literal global two-sided
C^r extension. Only the residual and its actual derivative bound are given. -/
theorem exists_regular_homeomorph (A : E ≃L[ℝ] F) (b : F) {r : ℝ} (hr : 1 ≤ r)
    (u : E → F) (regular : Regular (E := E) (F := F) r u) (k : ℝ≥0)
    (bound : ∀ x, ‖fderiv ℝ u x‖ ≤ k)
    (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹) :
    ∃ H : E ≃ₜ F, (∀ x, H x = A x+b+u x) ∧
      Regular (E := E) (F := F) r H ∧ Regular (E := F) (F := E) r H.symm := by
  have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hr)
  have du : Differentiable ℝ u := regular.differentiable.contDiff.differentiable
    (by exact_mod_cast (Nat.ne_of_gt order))
  let lip := lipschitz_of_derivative du bound
  exact ⟨homeomorph A b lip small, fun _ => rfl, regular_map A b regular,
    regular_inverse A b lip small hr regular⟩

end LeanShared.SmallAffinePerturbation
