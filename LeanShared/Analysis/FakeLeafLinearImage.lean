module
public import LeanShared.Analysis.FakeLeafFlatCondition
public import LeanShared.Analysis.NonlinearSecantLinearization
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import all LeanShared.Analysis.FakeLeafGeometry

public noncomputable section
open Set
open scoped RealInnerProductSpace
namespace LeanShared.FakeLeafLinearImage
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual adjoint of an invertible map, with invertibility derived. -/
@[expose] def adjointEquiv (A : E ≃L[ℝ] E) : E ≃L[ℝ] E := by
  have injective : Function.Injective A.toContinuousLinearMap.adjoint := by
    intro x y equal
    apply ext_inner_right ℝ
    intro z
    obtain ⟨v, rfl⟩ := A.surjective z
    simpa only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearEquiv.coe_coe] using
      congrArg (fun q => inner ℝ q v) equal
  exact (LinearEquiv.ofInjectiveEndo A.toContinuousLinearMap.adjoint.toLinearMap
    injective).toContinuousLinearEquiv

@[simp] theorem adjointEquiv_apply (A : E ≃L[ℝ] E) (x : E) :
    adjointEquiv A x = A.toContinuousLinearMap.adjoint x := rfl

theorem inverse_adjoint_pair (A : E ≃L[ℝ] E) (z p : E) :
    inner ℝ (A z) (adjointEquiv A.symm p) = inner ℝ z p := by
  rw [adjointEquiv_apply, ContinuousLinearMap.adjoint_inner_right]
  exact congrArg (fun q => inner ℝ q p) (A.symm_apply_apply z)

theorem planeError_le (P : Submodule ℝ E) (positive : 0 < Module.finrank ℝ P)
    (z : E) {ε : ℝ} (nonnegative : 0 ≤ ε)
    (bound : ∀ p ∈ P, |inner ℝ z p| ≤ ε * ‖z‖ * ‖p‖) :
    FakeLeafGeometry.planeError P z ≤ ε := by
  apply csSup_le (FakeLeafGeometry.planeErrorValues_nonempty P z positive)
  rintro r ⟨p, hp, hpzero, rfl⟩
  by_cases hz : z = 0
  · simpa [FakeLeafGeometry.normalized, hz] using nonnegative
  have zn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have pn : 0 < ‖p‖ := norm_pos_iff.mpr hpzero
  simp only [FakeLeafGeometry.normalized, inner_smul_left, inner_smul_right, conj_trivial]
  calc
    _ = ‖z‖⁻¹ * (‖p‖⁻¹ * inner ℝ z p) := by ring
    _ ≤ ‖z‖⁻¹ * (‖p‖⁻¹ * |inner ℝ z p|) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.mpr pn.le))
        (inv_nonneg.mpr zn.le)
    _ ≤ ‖z‖⁻¹ * (‖p‖⁻¹ * (ε * ‖z‖ * ‖p‖)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (bound p hp) (inv_nonneg.mpr pn.le))
        (inv_nonneg.mpr zn.le)
    _ = ε := by field_simp
/-- Cone-contained normal planes transform by the genuine inverse adjoint. -/
theorem transformed_plane {C C' : Set E} {ds : ℕ} (A : E ≃L[ℝ] E)
    (cone : ∀ v ∈ C, adjointEquiv A.symm v ∈ C')
    {P : Submodule ℝ E} (admissible : P ∈ FakeLeafGeometry.admissiblePlanes C ds) :
    P.map (adjointEquiv A.symm).toLinearMap ∈ FakeLeafGeometry.admissiblePlanes C' ds := by
  constructor
  · rintro q ⟨p, hp, rfl⟩
    exact cone p (admissible.1 hp)
  · exact (LinearEquiv.finrank_map_eq (adjointEquiv A.symm).toLinearEquiv P).trans admissible.2

/-- Infimum zero is transported without assuming that its minimizing normal
plane exists. Approximate source planes suffice. -/
theorem normalError_map_zero {C C' : Set E} {ds : ℕ} (positive : 0 < ds)
    (planes : (FakeLeafGeometry.admissiblePlanes C ds).Nonempty)
    (A : E ≃L[ℝ] E) (cone : ∀ v ∈ C, adjointEquiv A.symm v ∈ C')
    (z : E) (zero : FakeLeafGeometry.normalError C ds z = 0) :
    FakeLeafGeometry.normalError C' ds (A z) = 0 := by
  let H := adjointEquiv A.symm
  have targetPlanes : (FakeLeafGeometry.admissiblePlanes C' ds).Nonempty := by
    obtain ⟨P, hp⟩ := planes
    exact ⟨P.map H.toLinearMap, transformed_plane A cone hp⟩
  let K := ‖A.symm.toContinuousLinearMap‖ * ‖H.symm.toContinuousLinearMap‖
  have Kn : 0 ≤ K := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  apply le_antisymm _ (FakeLeafGeometry.normalError_nonneg positive targetPlanes _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨P, pc, pd, approx⟩ := FakeLeafGeometry.exists_approximate_normal_plane planes z zero
    (show 0 < ε / (K + 1) from div_pos hε (by linarith))
  let Q := P.map H.toLinearMap
  have qa : Q ∈ FakeLeafGeometry.admissiblePlanes C' ds := transformed_plane A cone ⟨pc, pd⟩
  have bound : ∀ q ∈ Q, |inner ℝ (A z) q| ≤
      (ε / (K + 1) * K) * ‖A z‖ * ‖q‖ := by
    rintro q ⟨p, hp, rfl⟩
    have zn : ‖z‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A z‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
        using A.symm.toContinuousLinearMap.le_opNorm (A z)
    have pn : ‖p‖ ≤ ‖H.symm.toContinuousLinearMap‖ * ‖H p‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
        using H.symm.toContinuousLinearMap.le_opNorm (H p)
    change |inner ℝ (A z) (H p)| ≤ (ε / (K + 1) * K) * ‖A z‖ * ‖H p‖
    rw [show inner ℝ (A z) (H p) = inner ℝ z p from inverse_adjoint_pair A z p]
    calc
      _ ≤ ε / (K + 1) * ‖z‖ * ‖p‖ := approx p hp
      _ ≤ ε / (K + 1) * (‖A.symm.toContinuousLinearMap‖ * ‖A z‖) *
          (‖H.symm.toContinuousLinearMap‖ * ‖H p‖) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left zn (div_nonneg hε.le (by linarith))) pn
          (norm_nonneg _) (mul_nonneg (div_nonneg hε.le (by linarith))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ = _ := by dsimp only [K]; ring
  have pe := planeError_le Q (qa.2.symm ▸ positive) (A z)
    (mul_nonneg (div_nonneg hε.le (by linarith)) Kn) bound
  have ne := csInf_le (FakeLeafGeometry.normalErrorValues_bddBelow C' positive (A z))
    (show FakeLeafGeometry.planeError Q (A z) ∈
      FakeLeafGeometry.normalErrorValues C' ds (A z) from ⟨Q, qa, rfl⟩)
  have smaller : ε / (K + 1) * K ≤ ε := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < K + 1 by linarith)).mpr
    nlinarith
  exact ne.trans (pe.trans (by simpa only [zero_add] using smaller))
/-- The literal outer supremum vanishes when every nonzero chord has zero
normal error; empty and singleton leaves are included. -/
theorem leafError_zero_of_chords {C : Set E} {ds : ℕ} (positive : 0 < ds)
    (planes : (FakeLeafGeometry.admissiblePlanes C ds).Nonempty) (Γ : Set E)
    (chords : ∀ x ∈ Γ, ∀ y ∈ Γ, x ≠ y →
      FakeLeafGeometry.normalError C ds (y - x) = 0) :
    FakeLeafGeometry.leafError C ds Γ = 0 := by
  have values : ∀ r ∈ FakeLeafGeometry.leafErrorValues C ds Γ, r = 0 := by
    rintro r ⟨x, hx, y, hy, different, rfl⟩
    exact chords x hx y hy different
  by_cases nonempty : (FakeLeafGeometry.leafErrorValues C ds Γ).Nonempty
  · apply le_antisymm
    · exact csSup_le nonempty (fun r hr => (values r hr).le)
    · obtain ⟨r, hr⟩ := nonempty
      rw [← values r hr]
      exact le_csSup (FakeLeafGeometry.leafErrorValues_bddAbove positive planes Γ) hr
  · simp only [FakeLeafGeometry.leafError, Set.not_nonempty_iff_eq_empty.mp nonempty,
      Real.sSup_empty]

/-- Actual nonlinear image secants are admissible under a robust inverse-adjoint
cone condition. No tangent-only replacement of the fake-leaf predicate occurs. -/
theorem nonlinear_image_zero {C C' : Set E} {ds : ℕ} (positive : 0 < ds)
    (planes : (FakeLeafGeometry.admissiblePlanes C ds).Nonempty)
    (f : E → E) (A : E ≃L[ℝ] E) (s : Set E) (convex : Convex ℝ s)
    {δ : ℝ} (nonnegative : 0 ≤ δ) (small : ‖A.symm.toContinuousLinearMap‖ * δ < 1)
    (differentiable : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (comparison : ∀ x ∈ s, ‖fderiv ℝ f x - A.toContinuousLinearMap‖ ≤ δ)
    (cone : ∀ B : E ≃L[ℝ] E,
      ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ ≤ δ →
      ∀ v ∈ C, adjointEquiv B.symm v ∈ C')
    {Γ : Set E} (inside : Γ ⊆ s) (fake : FakeLeafGeometry.leafError C ds Γ = 0) :
    FakeLeafGeometry.leafError C' ds (f '' Γ) = 0 := by
  have baseCone : ∀ v ∈ C, adjointEquiv A.symm v ∈ C' :=
    cone A (by simpa only [sub_self, norm_zero] using nonnegative)
  have targetPlanes : (FakeLeafGeometry.admissiblePlanes C' ds).Nonempty := by
    obtain ⟨P, hp⟩ := planes
    exact ⟨P.map (adjointEquiv A.symm).toLinearMap, transformed_plane A baseCone hp⟩
  apply leafError_zero_of_chords positive targetPlanes
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ different
  have sourceDifferent : x ≠ y := fun equal => different (congrArg f equal)
  have sourceZero := FakeLeafGeometry.normalError_eq_zero_of_leafError_zero positive planes
    fake hx hy sourceDifferent
  obtain ⟨B, close, secant⟩ := NonlinearSecantLinearization.exists_equiv_secant f A s convex
    nonnegative small differentiable comparison (inside hx) (inside hy)
  rw [← secant]
  exact normalError_map_zero positive planes B (cone B close) (y - x) sourceZero
end LeanShared.FakeLeafLinearImage
