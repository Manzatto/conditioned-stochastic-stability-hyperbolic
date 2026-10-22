module

public import LeanShared.Dynamics.FiniteMinimumPartition
public import LeanShared.Dynamics.FiniteBowenDistance

/-! Actual measurable Bowen/Voronoi cells from a finite separated spanning
family. Cells contain fine orbit balls and lie in coarse orbit balls;
the least-index convention resolves ties measurably. -/
public noncomputable section
open Set MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
open FiniteBowenDistance

@[expose] def bowenVoronoiPartition (T : X → X) (continuous : Continuous T)
    (centers : Fin k → X) (positiveK : 0 < k) (n : ℕ) : MeasurablePartition (X := X) k :=
  finiteMinimumPartition (fun i x => distance T n x (centers i))
    (fun i => (continuous_left T continuous n (centers i)).measurable) positiveK

theorem bowenVoronoi_atom_bound (T : X → X) (continuous : Continuous T)
    (centers : Fin k → X) (positiveK : 0 < k) (n : ℕ) (r : ℝ)
    (spanning : ∀ x, ∃ i, distance T n x (centers i) < r)
    (i : Fin k) (x : X) (member : x ∈ (bowenVoronoiPartition T continuous centers positiveK n).atom i) :
    distance T n x (centers i) < r := by
  obtain ⟨j, near⟩ := spanning x
  exact (member.1 j).trans_lt near

theorem bowenVoronoi_ball_mem (T : X → X) (continuous : Continuous T)
    (centers : Fin k → X) (positiveK : 0 < k) (n : ℕ) (r : ℝ) (positive : 0 < r)
    (separated : ∀ i j, i ≠ j → r ≤ distance T n (centers i) (centers j))
    (i : Fin k) (x : X) (near : distance T n x (centers i) < r / 3) :
    x ∈ (bowenVoronoiPartition T continuous centers positiveK n).atom i := by
  apply strict_minimum_mem_partition
  intro j different
  have apart := separated i j different.symm
  have tri := triangle T n (centers i) x (centers j)
  rw [symmetric T n (centers i) x] at tri
  linarith

theorem bowenVoronoi_atom_mesh (T : X → X) (continuous : Continuous T)
    (centers : Fin k → X) (positiveK : 0 < k) (n : ℕ) (r : ℝ)
    (spanning : ∀ x, ∃ i, distance T n x (centers i) < r)
    (i : Fin k) (x y : X)
    (hx : x ∈ (bowenVoronoiPartition T continuous centers positiveK n).atom i)
    (hy : y ∈ (bowenVoronoiPartition T continuous centers positiveK n).atom i) :
    ∀ j ≤ n, dist (T^[j] x) (T^[j] y) < 2 * r := by
  have first := bowenVoronoi_atom_bound T continuous centers positiveK n r spanning i x hx
  have second := bowenVoronoi_atom_bound T continuous centers positiveK n r spanning i y hy
  have tri := triangle T n x (centers i) y
  rw [symmetric T n (centers i) y] at tri
  have near : distance T n x y < 2 * r := by linarith
  exact (lt_iff T n x y _).mp near

end LeanShared.ThermodynamicDefinitions
