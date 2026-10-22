module
public import LeanShared.Analysis.SmallAffinePerturbation

/-! Quantitative bounds and actual parameter continuity for the global
inverse of a uniformly small affine perturbation. Its inverse is exactly
affine outside the affine image of the fixed residual support. -/
@[expose] public noncomputable section
open Set Filter Function
open scoped NNReal Topology
namespace LeanShared.SmallAffinePerturbation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def inverseConstant (A : E ≃L[ℝ] F) (k : ℝ≥0) : ℝ≥0 :=
  (‖A.symm.toContinuousLinearMap‖₊⁻¹-k)⁻¹

theorem inverse_lipschitz (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u) (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹) :
    LipschitzWith (inverseConstant A k) (homeomorph A b lip small).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  let H := homeomorph A b lip small
  have bound := ((approximates A b lip).antilipschitzWith small).le_mul_dist
    (⟨H.symm y, mem_univ _⟩ : (univ : Set E)) (⟨H.symm z, mem_univ _⟩ : (univ : Set E))
  change dist (H.symm y) (H.symm z) ≤ (inverseConstant A k : ℝ) *
    dist (map A b u (H.symm y)) (map A b u (H.symm z)) at bound
  have eqy : map A b u (H.symm y) = y := H.apply_symm_apply y
  have eqz : map A b u (H.symm z) = z := H.apply_symm_apply z
  rw [eqy, eqz] at bound
  exact bound

theorem inverse_dist_le (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u) (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (y : F) (x : E) :
    dist ((homeomorph A b lip small).symm y) x ≤
      (inverseConstant A k : ℝ) * dist y (map A b u x) := by
  have bound := (inverse_lipschitz A b lip small).dist_le_mul y (homeomorph A b lip small x)
  rw [Homeomorph.symm_apply_apply, homeomorph_apply] at bound
  exact bound

theorem inverse_eq_affine_of_zero (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u) (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (y : F) (zero : u (A.symm (y-b)) = 0) :
    (homeomorph A b lip small).symm y = A.symm (y-b) := by
  apply (homeomorph A b lip small).injective
  rw [Homeomorph.apply_symm_apply, homeomorph_apply]
  simp only [map, zero, add_zero, A.apply_symm_apply, sub_add_cancel]

theorem inverse_affine_off_image (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u) (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    {S : Set E} (support : Function.support u ⊆ S) (y : F)
    (outside : y ∉ (fun x => A x+b) '' S) :
    (homeomorph A b lip small).symm y = A.symm (y-b) := by
  have absent : A.symm (y-b) ∉ S := by
    intro member
    apply outside
    exact ⟨A.symm (y-b), member, by simp only [A.apply_symm_apply, sub_add_cancel]⟩
  apply inverse_eq_affine_of_zero A b lip small y
  by_contra nonzero
  exact absent (support nonzero)

/-- Pointwise continuity of the forward residual family and one common
small Lipschitz bound give genuine joint continuity of the actual inverse.
No continuity of a selected inverse is assumed. -/
theorem continuous_inverse_family {P : Type*} [TopologicalSpace P]
    (A : E ≃L[ℝ] F) (b : F) (u : P → E → F) (k : ℝ≥0)
    (lip : ∀ p, LipschitzWith k (u p))
    (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (continuous : ∀ x, Continuous (fun p => u p x)) :
    Continuous (fun q : P × F => (homeomorph A b (lip q.1) small).symm q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q₀
  let x₀ := (homeomorph A b (lip q₀.1) small).symm q₀.2
  have forward : Continuous (fun p => map A b (u p) x₀) :=
    continuous_const.add (continuous x₀)
  have upper : Continuous (fun q : P × F =>
      (inverseConstant A k : ℝ) * dist q.2 (map A b (u q.1) x₀)) :=
    continuous_const.mul (continuous_snd.dist (forward.comp continuous_fst))
  have atReference : map A b (u q₀.1) x₀ = q₀.2 :=
    (homeomorph A b (lip q₀.1) small).apply_symm_apply q₀.2
  have limit : Tendsto (fun q : P × F =>
      (inverseConstant A k : ℝ) * dist q.2 (map A b (u q.1) x₀)) (𝓝 q₀) (𝓝 0) := by
    simpa only [atReference, dist_self, mul_zero] using (upper.continuousAt (x := q₀)).tendsto
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg)
    (fun q => inverse_dist_le A b (lip q.1) small q.2 x₀) limit

end LeanShared.SmallAffinePerturbation
