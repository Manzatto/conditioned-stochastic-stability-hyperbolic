module
public import LeanShared.Analysis.ActualFiniteLabelledWord
public import LeanShared.Analysis.ActualWordChronology
import Mathlib.Tactic.Ring

/-! Exact finite-prefix product for the literal labelled ordinary action.
This retains the terminal factor and the zero-length word. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace LeanShared.ActualFiniteLabelledWord
open ActualFiniteRegularWord CylinderPrincipalCoefficient
variable {X Ω I : Type*} (F : Ω → X → X) (weights : I → X → ℂ)

theorem amplitude_eq_product_take (terminal : X → ℂ) (word : List (Ω × I)) (x : X) :
    amplitude F weights terminal word x =
      (∏ j : Fin word.length,
        weights (word.get j).2 (orbit (fun z : Ω × I => F z.1) (word.take j.val) x)) *
      terminal (orbit (fun z : Ω × I => F z.1) word x) := by
  induction word generalizing x with
  | nil => simp [amplitude, orbit]
  | cons z word ih =>
    rw [amplitude, ih]
    simp only [List.length_cons]
    rw [Fin.prod_univ_succ]
    simp only [List.length_cons, Fin.val_zero, List.take_zero, orbit, Fin.val_succ,
      List.take_succ_cons, List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ]
    ring

theorem amplitude_ofFn_eq_product (terminal : X → ℂ) {N : ℕ}
    (word : Fin N → Ω × I) (x : X) :
    amplitude F weights terminal (List.ofFn word) x =
      (∏ j : Fin N, weights (word j).2
        (prefixOrbit (fun z : Ω × I => F z.1) word j.val x)) *
      terminal (prefixOrbit (fun z : Ω × I => F z.1) word N x) := by
  rw [amplitude_eq_product_take, orbit_ofFn_eq_prefix]
  congr 1
  calc
    _ = ∏ j : Fin (List.ofFn word).length,
        weights (word ⟨j.val, by simpa only [List.length_ofFn] using j.isLt⟩).2
          (prefixOrbit (fun z : Ω × I => F z.1) word j.val x) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [List.get_eq_getElem, List.getElem_ofFn, ← prefixOrbit_eq_take]
    _ = _ := Fintype.prod_equiv (finCongr List.length_ofFn) _ _ (fun _ => rfl)

end LeanShared.ActualFiniteLabelledWord
