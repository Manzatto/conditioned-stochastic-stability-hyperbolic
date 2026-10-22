module
public import LeanShared.Analysis.ActualWordChronology

/-! Exact control-alphabet reindexing for the literal chronological map,
signed weight, and every prefix. In particular the physical control word
and the Fin N-indexed family with identity word have the same functions. -/
public noncomputable section
namespace LeanShared.ActualFiniteRegularWord
variable {G H X : Type*} (F : G → X → X) (g : X → ℝ) (index : H → G)

theorem reindex_orbit_list (w : List H) (x : X) :
    orbit F (w.map index) x = orbit (fun h => F (index h)) w x := by
  induction w generalizing x with
  | nil => rfl
  | cons h w ih => exact ih (F (index h) x)

theorem reindex_weight_list (w : List H) (x : X) :
    weight F g (w.map index) x = weight (fun h => F (index h)) g w x := by
  induction w generalizing x with
  | nil => rfl
  | cons h w ih =>
    change (g x : ℂ)*weight F g (w.map index) (F (index h) x) = _
    rw [ih]
    rfl

theorem reindex_orbit_ofFn {N : ℕ} (word : Fin N → G) (x : X) :
    orbit F (List.ofFn word) x =
      orbit (fun j : Fin N => F (word j)) (List.ofFn (fun j => j)) x := by
  simpa only [List.map_ofFn,Function.comp_def] using reindex_orbit_list F word (List.ofFn (fun j : Fin N => j)) x

theorem reindex_weight_ofFn {N : ℕ} (word : Fin N → G) (x : X) :
    weight F g (List.ofFn word) x =
      weight (fun j : Fin N => F (word j)) g (List.ofFn (fun j => j)) x := by
  simpa only [List.map_ofFn,Function.comp_def] using reindex_weight_list F g word (List.ofFn (fun j : Fin N => j)) x

end LeanShared.ActualFiniteRegularWord

namespace LeanShared.CylinderPrincipalCoefficient
variable {G X : Type*} (F : G → X → X)

theorem reindex_prefixOrbit {N : ℕ} (word : Fin N → G) (k : ℕ) (x : X) :
    prefixOrbit F word k x =
      prefixOrbit (fun j : Fin N => F (word j)) (fun j => j) k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < N
    · simp only [prefixOrbit,dite_eq_left hk,ih]
    · simp only [prefixOrbit,dite_eq_right hk,ih]

end LeanShared.CylinderPrincipalCoefficient
