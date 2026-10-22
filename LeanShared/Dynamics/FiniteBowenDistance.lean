module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Data.Finset.Lattice.Fold

/-! The literal maximum of finitely many orbit distances. This is a
continuous finite score used to construct actual Bowen/Voronoi cells;
no replacement of the ambient metric is made. -/
public noncomputable section
namespace LeanShared.FiniteBowenDistance
variable {X : Type*} [MetricSpace X]

@[expose] def distance (T : X → X) (n : ℕ) (x y : X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (n + 1) => dist (T^[j.val] x) (T^[j.val] y))

theorem coordinate_le (T : X → X) (n : ℕ) (x y : X) (j : Fin (n + 1)) :
    dist (T^[j.val] x) (T^[j.val] y) ≤ distance T n x y :=
  Finset.le_sup' (fun j : Fin (n + 1) => dist (T^[j.val] x) (T^[j.val] y)) (Finset.mem_univ j)

theorem nonnegative (T : X → X) (n : ℕ) (x y : X) : 0 ≤ distance T n x y :=
  (dist_nonneg : 0 ≤ dist x y).trans (by simpa using coordinate_le T n x y ⟨0, by omega⟩)

theorem le_iff (T : X → X) (n : ℕ) (x y : X) (r : ℝ) :
    distance T n x y ≤ r ↔ ∀ j ≤ n, dist (T^[j] x) (T^[j] y) ≤ r := by
  simp only [distance, Finset.sup'_le_iff, Finset.mem_univ, forall_const]
  exact ⟨fun bound j hj => bound ⟨j, by omega⟩, fun bound j => bound j.val (by omega)⟩

theorem lt_iff (T : X → X) (n : ℕ) (x y : X) (r : ℝ) :
    distance T n x y < r ↔ ∀ j ≤ n, dist (T^[j] x) (T^[j] y) < r := by
  simp only [distance, Finset.sup'_lt_iff, Finset.mem_univ, forall_const]
  exact ⟨fun bound j hj => bound ⟨j, by omega⟩, fun bound j => bound j.val (by omega)⟩

theorem symmetric (T : X → X) (n : ℕ) (x y : X) : distance T n x y = distance T n y x := by
  simp only [distance, dist_comm]

theorem triangle (T : X → X) (n : ℕ) (x y z : X) :
    distance T n x z ≤ distance T n x y + distance T n y z := by
  apply (le_iff T n x z _).mpr
  intro j hj
  exact (dist_triangle (T^[j] x) (T^[j] y) (T^[j] z)).trans
    (add_le_add (coordinate_le T n x y ⟨j, by omega⟩) (coordinate_le T n y z ⟨j, by omega⟩))

theorem continuous_left (T : X → X) (continuous : Continuous T) (n : ℕ) (y : X) :
    Continuous (fun x => distance T n x y) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun j _ => (continuous.iterate j.val).dist continuous_const)

end LeanShared.FiniteBowenDistance
