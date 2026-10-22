module

public import LeanShared.Analysis.ActualWordChronology
public import LeanShared.Analysis.ContinuousIntrinsicPrincipalDensity

/-! The intrinsic/list accumulated weight is exactly the product over the
same finite-prefix path used by cylinder distortion and pressure. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace LeanShared.ActualWordWeightProduct
open ActualFiniteRegularWord CylinderPrincipalCoefficient
variable {G X : Type*} (F : G → X → X)

theorem realWeight_eq_product_take (g : X → ℝ) (w : List G) (x : X) :
    ActualWordMicrolocalBound.realWeight F g w x =
      ∏ j : Fin w.length, g (orbit F (w.take j.val) x) := by
  induction w generalizing x with
  | nil => simp [ActualWordMicrolocalBound.realWeight]
  | cons a w ih =>
    rw [ActualWordMicrolocalBound.realWeight, ih]
    change g x * (∏ j : Fin w.length, g (orbit F (w.take j.val) (F a x))) =
      ∏ j : Fin (w.length + 1), g (orbit F ((a :: w).take j.val) x)
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, List.take_zero, orbit, Fin.val_succ, List.take_succ_cons]

theorem realWeight_ofFn_eq_product (g : X → ℝ) {N : ℕ} (word : Fin N → G) (x : X) :
    ActualWordMicrolocalBound.realWeight F g (List.ofFn word) x =
      ∏ j : Fin N, g (prefixOrbit F word j.val x) := by
  calc
    _ = ∏ j : Fin (List.ofFn word).length, g (prefixOrbit F word j.val x) := by
      rw [realWeight_eq_product_take]
      apply Finset.prod_congr rfl
      intro j _
      exact congrArg g (ActualFiniteRegularWord.prefixOrbit_eq_take F word j.val x).symm
    _ = _ := Fintype.prod_equiv (finCongr (List.length_ofFn)) _ _ (fun _ => rfl)

theorem intrinsic_weight_eq_product (g : X → ℝ) {N : ℕ} (word : Fin N → G) (x : X) :
    IntrinsicPrincipalDensity.weight F g (List.ofFn word) x =
      ∏ j : Fin N, g (prefixOrbit F word j.val x) :=
  (ContinuousIntrinsicPrincipalDensity.weight_eq F g (List.ofFn word) x).trans
    (realWeight_ofFn_eq_product F g word x)

theorem intrinsic_weight_eq_cylinder (g : X → ℝ) (hg : ∀ x, 0 ≤ g x)
    {N : ℕ} (word : Fin N → G) (x : X) :
    IntrinsicPrincipalDensity.weight F g (List.ofFn word) x = wordWeight F g (word, x) := by
  rw [intrinsic_weight_eq_product]
  simp only [wordWeight, abs_of_nonneg (hg _)]

end LeanShared.ActualWordWeightProduct
