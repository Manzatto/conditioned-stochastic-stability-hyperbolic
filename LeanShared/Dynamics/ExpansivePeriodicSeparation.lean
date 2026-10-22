module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Topology.Homeomorph.Defs
import Lean.Elab.Tactic.Omega

/-! Positive-period points are separated at the expansivity scale over
one forward period. Inverse observations are recovered from the same
finite cycle, so no additional negative-time hypothesis is supplied. -/
public section
namespace LeanShared.ExpansivePeriodicSeparation
open Function Set
variable {X : Type*} [MetricSpace X]

theorem inverse_time (T : X ≃ₜ X) (p j : ℕ) (x : X)
    (fixed : (T : X → X)^[p] x = x) (hj : j ≤ p) :
    (T.symm : X → X)^[j] x = (T : X → X)^[p - j] x := by
  have split : (T : X → X)^[p] x =
      (T : X → X)^[j] ((T : X → X)^[p - j] x) := by
    rw [← iterate_add_apply, Nat.add_sub_of_le hj]
  calc
    _ = (T.symm : X → X)^[j] ((T : X → X)^[p] x) := congrArg _ fixed.symm
    _ = _ := by rw [split]; exact T.left_inv.iterate j _

theorem one_period_detects (T : X ≃ₜ X) (K : Set X) (c : ℝ)
    (expansive : ∀ x ∈ K, ∀ y ∈ K, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (p : ℕ) (positiveP : 0 < p) (x : X) (hx : x ∈ K)
    (y : X) (hy : y ∈ K) (fixedX : (T : X → X)^[p] x = x)
    (fixedY : (T : X → X)^[p] y = y)
    (near : ∀ j < p, dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c) : x = y := by
  have forward (j : ℕ) : dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c := by
    rw [← IsPeriodicPt.iterate_mod_apply fixedX j, ← IsPeriodicPt.iterate_mod_apply fixedY j]
    exact near (j % p) (Nat.mod_lt _ positiveP)
  have inverseX : (T.symm : X → X)^[p] x = x := by
    have same := congrArg ((T.symm : X → X)^[p]) fixedX
    have cancel : (T.symm : X → X)^[p] ((T : X → X)^[p] x) = x :=
      Function.LeftInverse.iterate (fun z => T.symm_apply_apply z) p x
    rw [cancel] at same
    exact same.symm
  have inverseY : (T.symm : X → X)^[p] y = y := by
    have same := congrArg ((T.symm : X → X)^[p]) fixedY
    have cancel : (T.symm : X → X)^[p] ((T : X → X)^[p] y) = y :=
      Function.LeftInverse.iterate (fun z => T.symm_apply_apply z) p y
    rw [cancel] at same
    exact same.symm
  apply expansive x hx y hy
  intro j
  refine ⟨forward j, ?_⟩
  rw [← IsPeriodicPt.iterate_mod_apply inverseX j, ← IsPeriodicPt.iterate_mod_apply inverseY j,
    inverse_time T p (j % p) x fixedX (Nat.mod_lt _ positiveP).le,
    inverse_time T p (j % p) y fixedY (Nat.mod_lt _ positiveP).le]
  exact forward (p - j % p)

theorem separated (T : X ≃ₜ X) (K : Set X) (c : ℝ)
    (expansive : ∀ x ∈ K, ∀ y ∈ K, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (p : ℕ) (positiveP : 0 < p) (s : Finset X)
    (member : ∀ x ∈ s, x ∈ K) (fixed : ∀ x ∈ s, (T : X → X)^[p] x = x) :
    ThermodynamicDefinitions.Separated T K p c s := by
  refine ⟨member, fun x hx y hy different => ?_⟩
  by_contra failed
  push Not at failed
  exact different (one_period_detects T K c expansive p positiveP x (member x hx) y (member y hy)
    (fixed x hx) (fixed y hy) (fun j hj => (failed j hj).le))

end LeanShared.ExpansivePeriodicSeparation
