module
public import LeanShared.Analysis.IntrinsicSplittingFactors

/-! Multiplicativity of the actual transported unstable volume Jacobian
on point-dependent Hilbert tangent fibers. No isometric frames are chosen. -/
@[expose] public noncomputable section
open Set
namespace LeanShared.IntrinsicPrincipalDensity
variable {G M : Type*} (F : G → M → M)
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)]
  (D : ∀ a x, E x ≃L[ℝ] E (F a x))

private theorem normDet_domRestrict_congr (x y : M) (A : E x →ₗ[ℝ] E y)
    (U V : Submodule ℝ (E x)) (h : U = V) :
    (A.domRestrict U).normDet = (A.domRestrict V).normDet := by
  subst V
  rfl

theorem unstableJacobian_eq_domRestrict (word : List G) (x : M) (U : Submodule ℝ (E x)) :
    unstableJacobian F E D word x U =
      ((derivative F E D word x).toLinearMap.domRestrict U).normDet := by
  exact LinearMap.normDet_codRestrict _

theorem unstableJacobian_cons (a : G) (word : List G) (x : M) (U : Submodule ℝ (E x)) :
    unstableJacobian F E D (a :: word) x U =
      unstableJacobian F E D word (F a x) (U.map (D a x).toLinearMap) *
        ((D a x).toLinearMap.domRestrict U).normDet := by
  rw [unstableJacobian_eq_domRestrict, unstableJacobian_eq_domRestrict]
  change (((derivative F E D word (F a x)).toLinearMap).comp
    ((D a x).toLinearMap.domRestrict U)).normDet = _
  rw [LinearMap.normDet_comp]
  have hrange : ((D a x).toLinearMap.domRestrict U).range = U.map (D a x).toLinearMap := by
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      exact Submodule.mem_map.mpr ⟨u, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  exact congrArg (fun r : ℝ => r * ((D a x).toLinearMap.domRestrict U).normDet)
    (normDet_domRestrict_congr E (F a x) (orbit F word (F a x)) _ _ _ hrange)

/-- On an invariant actual subbundle the chronological Jacobian splits
into its literal successive one-step factors. -/
theorem unstableJacobian_cons_of_invariant (K : Set M)
    (U : (x : M) → Submodule ℝ (E x))
    (hinv : ∀ a x, x ∈ K → (U x).map (D a x).toLinearMap = U (F a x))
    (a : G) (word : List G) (x : M) (hx : x ∈ K) :
    unstableJacobian F E D (a :: word) x (U x) =
      ((D a x).toLinearMap.domRestrict (U x)).normDet *
        unstableJacobian F E D word (F a x) (U (F a x)) := by
  rw [unstableJacobian_cons, hinv a x hx, mul_comm]

end LeanShared.IntrinsicPrincipalDensity
