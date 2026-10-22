module

public import LeanShared.Analysis.ActualFiniteRegularWord
public import LeanShared.Analysis.CylinderPrincipalCoefficient

/-! Exact chronological agreement of the actual transfer list word and
finite-prefix cylinders. This supplies continuity for the same nonlinear
word appearing in the manifold local transfer matrix. -/

@[expose] public section
namespace LeanShared.ActualFiniteRegularWord
open CylinderPrincipalCoefficient
variable {G X : Type*} (F : G → X → X)

theorem orbit_append (w v : List G) (x : X) :
    orbit F (w ++ v) x = orbit F v (orbit F w x) := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih => exact ih (F a x)

theorem prefixOrbit_eq_take {N : ℕ} (word : Fin N → G) (k : ℕ) (x : X) :
    prefixOrbit F word k x = orbit F ((List.ofFn word).take k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < N
    · have hk' : k < (List.ofFn word).length := by simpa only [List.length_ofFn] using hk
      rw [prefixOrbit, dite_eq_left hk, List.take_succ_eq_append_getElem hk', orbit_append]
      simpa only [orbit, List.getElem_ofFn] using congrArg (F (word ⟨k, hk⟩)) ih
    · have hle : (List.ofFn word).length ≤ k := by
        simpa only [List.length_ofFn] using Nat.le_of_not_gt hk
      simpa only [prefixOrbit, dite_eq_right hk,
        List.take_of_length_le hle, List.take_of_length_le (hle.trans (Nat.le_succ k))] using ih

theorem orbit_ofFn_eq_prefix {N : ℕ} (word : Fin N → G) (x : X) :
    orbit F (List.ofFn word) x = prefixOrbit F word N x := by
  simpa only [List.take_of_length_le (show (List.ofFn word).length ≤ N by simp)] using
    (prefixOrbit_eq_take F word N x).symm

variable [TopologicalSpace G] [TopologicalSpace X]

theorem continuous_orbit_ofFn (hF : Continuous (fun z : G × X => F z.1 z.2)) (N : ℕ) :
    Continuous (fun z : (Fin N → G) × X => orbit F (List.ofFn z.1) z.2) := by
  simpa only [orbit_ofFn_eq_prefix] using continuous_prefixOrbit F hF N N

end LeanShared.ActualFiniteRegularWord
