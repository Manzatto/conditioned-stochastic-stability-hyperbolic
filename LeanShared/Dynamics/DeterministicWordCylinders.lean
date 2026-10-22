module
public import LeanShared.Dynamics.FiniteWordCylinders
public import Mathlib.Data.Fin.Tuple.Basic

/-! Literal deterministic matching: the N-step chronological word observes
N+1 points, while BT's N-letter open cylinder observes N points. The extra
terminal observation is exactly intersection with one inverse-image chart. -/
@[expose] public noncomputable section
open Set Function
namespace LeanShared.DeterministicWordCylinders
open CylinderPrincipalCoefficient
variable {G X J : Type*} [TopologicalSpace G] [TopologicalSpace X]

omit [TopologicalSpace G] [TopologicalSpace X] in
theorem prefix_constant (F : G → X → X) (a : G) (N j : ℕ) (hj : j ≤ N) (x : X) :
    prefixOrbit F (fun _ : Fin N => a) j x = (F a)^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [prefixOrbit, dite_eq_left (show j < N by omega), ih (by omega), iterate_succ_apply']

/-- An N-letter open orbit cylinder, with precisely times 0,...,N-1. -/
def cylinder (T : X → X) (charts : J → Set X) (N : ℕ) (labels : Fin N → J) : Set X :=
  {x | ∀ j : Fin N, T^[j.val] x ∈ charts (labels j)}

def survivors (T : X → X) (K : Set X) (N : ℕ) : Set X :=
  {x | ∀ j : Fin N, T^[j.val] x ∈ K}

omit [TopologicalSpace G] [TopologicalSpace X] in
theorem cylinder_fiber (F : G → X → X) (a : G) (charts : J → Set X)
    (N : ℕ) (labels : Fin (N + 1) → J) :
    (fun x => ((fun _ : Fin N => a), x)) ⁻¹'
      FiniteWordCylinders.cylinder F charts N labels = cylinder (F a) charts (N + 1) labels := by
  ext x
  change (∀ j : Fin (N + 1), prefixOrbit F (fun _ : Fin N => a) j.val x ∈ charts (labels j)) ↔ _
  simp only [prefix_constant F a N _ (Nat.le_of_lt_succ (Fin.isLt _)) x]
  rfl

omit [TopologicalSpace G] [TopologicalSpace X] in
theorem survivors_fiber (F : G → X → X) (a : G) (K : Set X) (N : ℕ) :
    fiber K (FiniteWordCylinders.survivors F K N) (fun _ => a) =
      survivors (F a) K (N + 1) := by
  ext x
  change (x ∈ K ∧ ∀ j : Fin (N + 1), prefixOrbit F (fun _ : Fin N => a) j.val x ∈ K) ↔ _
  simp only [prefix_constant F a N _ (Nat.le_of_lt_succ (Fin.isLt _)) x]
  constructor
  · exact fun h => h.2
  · intro hx
    exact ⟨hx ⟨0, Nat.succ_pos _⟩, hx⟩

omit [TopologicalSpace G] [TopologicalSpace X] in
theorem cylinder_snoc (T : X → X) (charts : J → Set X) (N : ℕ)
    (labels : Fin N → J) (last : J) :
    cylinder T charts (N + 1) (Fin.snoc labels last) =
      cylinder T charts N labels ∩ (T^[N]) ⁻¹' charts last := by
  ext x
  simp only [cylinder, mem_ofPred_eq, mem_inter_iff, mem_preimage, Fin.forall_iff_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, and_comm]

end LeanShared.DeterministicWordCylinders
