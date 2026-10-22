module

public import LeanShared.Dynamics.ClosedRelationFiniteDetection
public import LeanShared.Geometry.DiffeomorphismIterates

/-! Consecutive n-step Bowen relations separate all bilateral orbits of
T^n at the ORIGINAL expansivity radius. This supplies block generators
without a new metric or a radius shrinking with n. -/
public noncomputable section
open Set Function
namespace LeanShared.BlockRelationExpansivity
variable {X : Type*} [MetricSpace X]

def relation (T : X ≃ₜ X) (c : ℝ) (n : ℕ) : Set (X × X) :=
  {z | ∀ j < n, dist (T^[j] z.1) (T^[j] z.2) ≤ c}

theorem relation_closed (T : X ≃ₜ X) (c : ℝ) (n : ℕ) :
    IsClosed (relation T c n) := by
  have same : relation T c n = ⋂ j : ℕ, ⋂ (_ : j < n),
      {z : X × X | dist (T^[j] z.1) (T^[j] z.2) ≤ c} := by
    ext z; simp only [relation, mem_ofPred_eq, mem_iInter]
  rw [same]
  exact isClosed_iInter (fun j => isClosed_iInter (fun _ =>
    isClosed_le (((T.continuous.iterate j).comp continuous_fst).dist
      ((T.continuous.iterate j).comp continuous_snd)) continuous_const))

private theorem backward_indices (n k : ℕ) (positive : 0 < n) :
    ∃ q r : ℕ, r < n ∧ n * q = k + r := by
  by_cases zero : k % n = 0
  · refine ⟨k / n, 0, positive, ?_⟩
    have h := Nat.mod_add_div k n
    omega
  · refine ⟨k / n + 1, n - k % n, ?_, ?_⟩
    · have small := Nat.mod_lt k positive
      omega
    · have h := Nat.mod_add_div k n
      have small := Nat.mod_lt k positive
      rw [Nat.mul_add, Nat.mul_one]
      omega

theorem separates (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (n : ℕ) (positive : 0 < n) :
    ∀ x y, (∀ q : ℕ,
      ((T^n : X ≃ₜ X)^[q] x, (T^n : X ≃ₜ X)^[q] y) ∈ relation T c n ∧
      (((T^n).symm : X → X)^[q] x, ((T^n).symm : X → X)^[q] y) ∈ relation T c n) → x = y := by
  intro x y close
  apply expansive x y
  intro k
  constructor
  · have bounded := (close (k / n)).1 (k % n) (Nat.mod_lt k positive)
    change dist (T^[k % n] ((T^n : X ≃ₜ X)^[k / n] x))
      (T^[k % n] ((T^n : X ≃ₜ X)^[k / n] y)) ≤ c at bounded
    rw [DiffeomorphismIterates.coe_pow, ← iterate_mul, ← iterate_add_apply,
      ← iterate_add_apply, Nat.mod_add_div] at bounded
    exact bounded
  · obtain ⟨q, r, small, indices⟩ := backward_indices n k positive
    have bounded := (close q).2 r small
    change dist (T^[r] (((T^n).symm : X → X)^[q] x))
      (T^[r] (((T^n).symm : X → X)^[q] y)) ≤ c at bounded
    rw [DiffeomorphismIterates.coe_symm_pow, ← iterate_mul] at bounded
    have cancel (z : X) : (T : X → X)^[r] ((T.symm : X → X)^[n * q] z) =
        (T.symm : X → X)^[k] z := by
      rw [indices, Nat.add_comm k r, iterate_add_apply]
      exact T.right_inv.iterate r _
    rw [cancel, cancel] at bounded
    exact bounded

end LeanShared.BlockRelationExpansivity
