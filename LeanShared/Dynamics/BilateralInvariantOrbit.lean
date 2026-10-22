module
public import LeanShared.Dynamics.BilateralHomeomorphismOrbit
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Exact bilateral reference orbits in invariant subsets and the all-integer
metric bound derived from the original forward/inverse natural iterate bounds. -/
public section
open Set
namespace LeanShared.BilateralHomeomorphismOrbit
variable {X : Type*} [TopologicalSpace X]

theorem pow_orbit_mem (T : X ≃ₜ X) (S : Set X) (invariant : T '' S=S)
    (x : X) (inside : x ∈ S) (N : ℕ) (n : ℤ) : orbit (T^N) x n ∈ S := by
  have forward : MapsTo T S S := fun y hy => invariant ▸ mem_image_of_mem T hy
  have backward : MapsTo T.symm S S := by
    intro y hy
    rw [← invariant] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    simpa only [T.symm_apply_apply] using hz
  cases n with
  | ofNat j =>
    change orbit (T^N) x (j:ℤ) ∈ S
    rw [pow_nat_time]
    exact backward.iterate (N*j) inside
  | negSucc j =>
    change orbit (T^N) x (-((j+1:ℕ):ℤ)) ∈ S
    rw [pow_neg_nat_time]
    exact forward.iterate (N*(j+1)) inside

theorem pow_dist_le {M : Type*} [PseudoMetricSpace M] (T : M ≃ₜ M)
    (N : ℕ) (x y : M) (r : ℝ)
    (forward : ∀ j : ℕ, dist ((T : M → M)^[j] x) ((T : M → M)^[j] y) ≤ r)
    (backward : ∀ j : ℕ, dist ((T.symm : M → M)^[j] x) ((T.symm : M → M)^[j] y) ≤ r)
    (n : ℤ) : dist (orbit (T^N) x n) (orbit (T^N) y n) ≤ r := by
  cases n with
  | ofNat j =>
    change dist (orbit (T^N) x (j:ℤ)) (orbit (T^N) y (j:ℤ)) ≤ r
    rw [pow_nat_time,pow_nat_time]
    exact backward (N*j)
  | negSucc j =>
    change dist (orbit (T^N) x (-((j+1:ℕ):ℤ))) (orbit (T^N) y (-((j+1:ℕ):ℤ))) ≤ r
    rw [pow_neg_nat_time,pow_neg_nat_time]
    exact forward (N*(j+1))
end LeanShared.BilateralHomeomorphismOrbit
