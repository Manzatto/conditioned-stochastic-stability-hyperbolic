module

public import LeanShared.Analysis.IntrinsicPrincipalDensity

/-! Bounds for the literal word derivative factors from invariant splitting
and pointwise differential estimates. No independent scalar principal factor
is introduced. These lemmas apply to the actual tangent derivative word. -/

@[expose] public noncomputable section
open Set
namespace LeanShared.IntrinsicPrincipalDensity

variable {G M : Type*} (F : G → M → M)
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)]
  (D : ∀ a x, E x ≃L[ℝ] E (F a x))

omit [∀ x, FiniteDimensional ℝ (E x)] in
/-- One-step invariance propagates along the literal chronological word. -/
theorem derivative_map_invariant (K : Set M)
    (hK : ∀ a, MapsTo (F a) K K)
    (S : (x : M) → Submodule ℝ (E x))
    (hinvariant : ∀ a x, x ∈ K → (S x).map (D a x).toLinearMap = S (F a x))
    (word : List G) (x : M) (hx : x ∈ K) :
    (S x).map (derivative F E D word x).toLinearMap = S (orbit F word x) := by
  induction word generalizing x with
  | nil =>
    change (S x).map (LinearMap.id : E x →ₗ[ℝ] E x) = S x
    exact Submodule.map_id _
  | cons a word ih =>
    change (S x).map ((derivative F E D word (F a x)).toLinearMap.comp
      (D a x).toLinearMap) = S (orbit F word (F a x))
    rw [Submodule.map_comp, hinvariant a x hx]
    exact ih (F a x) (hK a hx)

omit [∀ x, FiniteDimensional ℝ (E x)] in
/-- Invariance and injectivity identify the stable preimage used in the
principal density with the initial stable fiber. -/
theorem stablePreimage_eq_of_invariant (word : List G) (x : M)
    (Sx : Submodule ℝ (E x)) (Sy : Submodule ℝ (E (orbit F word x)))
    (hinvariant : Sx.map (derivative F E D word x).toLinearMap = Sy) :
    stablePreimage F E D word x Sy = Sx := by
  ext v
  change derivative F E D word x v ∈ Sy ↔ v ∈ Sx
  rw [← hinvariant]
  constructor
  · rintro ⟨w, hw, heq⟩
    exact (derivative F E D word x).injective heq ▸ hw
  · intro hv
    exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩

omit [∀ x, FiniteDimensional ℝ (E x)] in
/-- A genuine pointwise contraction on the invariant stable fiber bounds the
restricted operator norm occurring in the intrinsic principal density. -/
theorem stableFactor_le_of_invariant (word : List G) (x : M)
    (Sx : Submodule ℝ (E x)) (Sy : Submodule ℝ (E (orbit F word x)))
    (hinvariant : Sx.map (derivative F E D word x).toLinearMap = Sy)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v ∈ Sx, ‖derivative F E D word x v‖ ≤ C * ‖v‖) :
    stableFactor F E D word x Sy ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  exact hbound v.val ((stablePreimage_eq_of_invariant F E D word x Sx Sy hinvariant) ▸ v.property)

omit [∀ x, FiniteDimensional ℝ (E x)] in
/-- A genuine backward differential bound on the transported unstable fiber
bounds the inverse norm used by the actual intrinsic density. -/
theorem inverseFactor_le_of_invariant (word : List G) (x : M)
    (Ux : Submodule ℝ (E x)) (Uy : Submodule ℝ (E (orbit F word x)))
    (hinvariant : Ux.map (derivative F E D word x).toLinearMap = Uy)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v ∈ Uy, ‖(derivative F E D word x).symm v‖ ≤ C * ‖v‖) :
    inverseFactor F E D word x Ux ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  exact hbound v.val (hinvariant ▸ v.property)

end LeanShared.IntrinsicPrincipalDensity
