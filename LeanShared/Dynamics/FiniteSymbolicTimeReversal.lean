module

public import LeanShared.Dynamics.FiniteSymbolicAtomTransitions

/-! Time reversal of literal graph paths and shadowing codes.  Reversing
the edge relation and the integer word conjugates the shift to its
inverse; cylinder images and the underlying coded points are preserved.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X] {R : A → A → Prop}

/-- Reversing a bilateral word reverses its directed edges. -/
@[expose] def reversePath (R : A → A → Prop) : Path R ≃ₜ Path (fun i j => R j i) where
  toFun a := ⟨fun n => a.val (-n), fun n => by
    have index : -(n + 1) + 1 = -n := by omega
    simpa only [index] using a.property (-(n + 1))⟩
  invFun a := ⟨fun n => a.val (-n), fun n => by
    have index : -(n + 1) + 1 = -n := by omega
    simpa only [index] using a.property (-(n + 1))⟩
  left_inv a := by apply Subtype.ext; funext n; exact congrArg a.val (neg_neg n)
  right_inv a := by apply Subtype.ext; funext n; exact congrArg a.val (neg_neg n)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun n => (continuous_apply (-n)).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun n => (continuous_apply (-n)).comp continuous_subtype_val)

@[simp] theorem reversePath_apply (a : Path R) (n : ℤ) :
    (reversePath R a).val n = a.val (-n) := rfl

@[simp] theorem reversePath_symm_apply (a : Path (fun i j => R j i)) (n : ℤ) :
    ((reversePath R).symm a).val n = a.val (-n) := rfl

theorem reversePath_shift (a : Path (fun i j => R j i)) :
    (reversePath R).symm (shift (fun i j => R j i) a) = (shift R).symm ((reversePath R).symm a) := by
  apply Subtype.ext
  funext n
  change a.val (-n + 1) = a.val (-(n - 1))
  exact congrArg a.val (by omega : -n + 1 = -(n - 1))

/-- The reversed graph codes the inverse homeomorphism. -/
@[expose] def reverseCode (code : Path R → X) : Path (fun i j => R j i) → X :=
  code ∘ (reversePath R).symm

theorem reverseCode_intertwines (T : X ≃ₜ X) (code : Path R → X)
    (intertwines : ∀ a, code (shift R a) = T (code a))
    (a : Path (fun i j => R j i)) :
    reverseCode code (shift (fun i j => R j i) a) = T.symm (reverseCode code a) := by
  change code ((reversePath R).symm (shift (fun i j => R j i) a)) =
    T.symm (code ((reversePath R).symm a))
  rw [reversePath_shift]
  exact code_shift_inverse T code intertwines _

theorem orbit_symm (T : X ≃ₜ X) (x : X) (n : ℤ) : orbit T.symm x n = orbit T x (-n) := by
  simp only [orbit, neg_neg]
  rw [show T.symm = T⁻¹ from rfl, inv_zpow, ← zpow_neg, neg_neg]

theorem reverseCode_near (T : X ≃ₜ X) (center : A → X) (code : Path R → X) (ε : ℝ)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (a : Path (fun i j => R j i)) (n : ℤ) :
    dist (orbit T.symm (reverseCode code a) n) (center (a.val (-n))) ≤ ε := by
  rw [orbit_symm]
  simpa only [reverseCode, Function.comp_apply, reversePath_symm_apply, neg_neg] using
    near ((reversePath R).symm a) (-n)

omit [MetricSpace X] in
theorem reverseCode_rectangle (code : Path R → X) (i : A) :
    rectangle (reverseCode code) i = rectangle code i := by
  ext x
  constructor
  · rintro ⟨a, symbol, coded⟩
    refine ⟨(reversePath R).symm a, ?_, coded⟩
    change a.val (-0) = i
    exact symbol
  · rintro ⟨a, symbol, coded⟩
    refine ⟨reversePath R a, ?_, ?_⟩
    · change a.val (-0) = i
      exact symbol
    · simpa only [reverseCode, Function.comp_apply, Homeomorph.symm_apply_apply] using coded

end LeanShared.BilateralShadowingCoding
