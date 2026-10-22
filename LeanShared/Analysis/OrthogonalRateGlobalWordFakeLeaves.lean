module
public import LeanShared.Analysis.OrthogonalDiagonalRateFakeLeafImage
public import LeanShared.Analysis.CylinderPrincipalCoefficient

/-! Literal chronological words of the actual globally extended maps
preserve the full fake-leaf condition, with the same fixed cone for every
word length. All maps and all prefix maps are global homeomorphisms. -/
public noncomputable section
namespace LeanShared.OrthogonalRateGlobalWordFakeLeaves
open Set OrthogonalProductCoordinates CylinderPrincipalCoefficient
variable {G X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

@[expose] def prefixHomeomorph (H : G → E ≃ₜ E) {N : ℕ} (word : Fin N → G) : ℕ → E ≃ₜ E
  | 0 => Homeomorph.refl E
  | k+1 => if hk : k<N then (prefixHomeomorph H word k).trans (H (word ⟨k,hk⟩))
    else prefixHomeomorph H word k

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem prefixHomeomorph_coe (H : G → E ≃ₜ E) {N : ℕ} (word : Fin N → G) (k : ℕ) :
    (prefixHomeomorph H word k : E → E) = prefixOrbit (fun a => (H a : E → E)) word k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k<N
    · funext x
      simp only [prefixHomeomorph, prefixOrbit, dite_eq_left hk]
      change H (word ⟨k,hk⟩) (prefixHomeomorph H word k x) = _
      rw [← ih]
    · simp only [prefixHomeomorph, prefixOrbit, dite_eq_right hk, ih]

theorem whole_word_image_zero
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (positiveDimension : 0 < Module.finrank ℝ Y)
    (a K : ℝ) (positive : 0 < a) (contracting : a < 1) (nonnegativeK : 0 ≤ K)
    (U : G → X ≃L[ℝ] X) (S : G → Y ≃L[ℝ] Y)
    (stable : ∀ g, ‖(S g).toContinuousLinearMap‖ ≤ a)
    (unstable : ∀ g, ‖(U g).symm.toContinuousLinearMap‖ ≤ a)
    (inverseBound : ∀ g, ‖(diagonal dimension (U g) (S g)).symm.toContinuousLinearMap‖ ≤ K)
    (H : G → E ≃ₜ E) (differentiable : ∀ g, Differentiable ℝ (H g))
    (close : ∀ g x, ‖fderiv ℝ (H g) x - (diagonal dimension (U g) (S g)).toContinuousLinearMap‖ ≤
      OrthogonalDiagonalRatePerturbation.radius a K)
    {Γ : Set E} (fake : FakeLeafGeometry.leafError
      (ProjectionConeTransversality.cone (firstProjection dimension) (ProjectionConeRateMargin.opening a))
      (Module.finrank ℝ Y) Γ = 0)
    {N : ℕ} (word : Fin N → G) (k : ℕ) :
    FakeLeafGeometry.leafError
      (ProjectionConeTransversality.cone (firstProjection dimension) (ProjectionConeRateMargin.opening a))
      (Module.finrank ℝ Y) (prefixHomeomorph H word k '' Γ) = 0 := by
  induction k with
  | zero =>
    change FakeLeafGeometry.leafError _ _ ((fun x : E => x) '' Γ) = 0
    have identityImage : (fun x : E => x) '' Γ = Γ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [identityImage]
    exact fake
  | succ k ih =>
    by_cases hk : k<N
    · have step := OrthogonalDiagonalRateFakeLeafImage.nonlinear_image_zero dimension positiveDimension
        a K positive contracting nonnegativeK (U (word ⟨k,hk⟩)) (S (word ⟨k,hk⟩))
        (stable _) (unstable _) (inverseBound _) (H (word ⟨k,hk⟩)) univ convex_univ
        (fun x _ => differentiable _ x) (fun x _ => close _ x) (subset_univ _) ih
      rw [prefixHomeomorph, dite_eq_left hk]
      change FakeLeafGeometry.leafError _ _
        (((H (word ⟨k,hk⟩) : E → E) ∘ (prefixHomeomorph H word k : E → E)) '' Γ) = 0
      have imageEq : ((H (word ⟨k,hk⟩) : E → E) ∘ (prefixHomeomorph H word k : E → E)) '' Γ =
          H (word ⟨k,hk⟩) '' (prefixHomeomorph H word k '' Γ) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨prefixHomeomorph H word k y, ⟨y, hy, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨z, hz, rfl⟩
      rw [imageEq]
      exact step
    · simpa only [prefixHomeomorph, dite_eq_right hk] using ih

end LeanShared.OrthogonalRateGlobalWordFakeLeaves
