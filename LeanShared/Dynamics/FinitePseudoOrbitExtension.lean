module
public import LeanShared.Dynamics.EntireOrbitIdentity
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! A finite pseudo-orbit extends to an entire pseudo-orbit with exactly the
same one-step error, following genuine orbits outside its two endpoints. -/
public noncomputable section
namespace LeanShared.FinitePseudoOrbitExtension
open BilateralHomeomorphismOrbit
variable {X:Type*} [MetricSpace X] (T:X≃ₜX) {n:ℕ} (p:Fin (n+1)→X)

@[expose] def reference (i:ℤ) : X :=
  if hleft : i ≤ 0 then orbit T (p ⟨0,Nat.zero_lt_succ n⟩) i
  else if hright : (n:ℤ) ≤ i then orbit T (p ⟨n,Nat.lt_succ_self n⟩) (i-(n:ℤ))
  else p ⟨i.toNat,by omega⟩

theorem nonpositive (i:ℤ) (hi:i≤0) :
    reference T p i=orbit T (p ⟨0,Nat.zero_lt_succ n⟩) i := by
  unfold reference
  split_ifs; rfl

theorem above (i:ℤ) (hi:(n:ℤ)≤ i) :
    reference T p i=orbit T (p ⟨n,Nat.lt_succ_self n⟩) (i-(n:ℤ)) := by
  unfold reference
  split_ifs with hleft
  · have hn:n=0 := by omega
    subst n
    have zero:i=0 := by omega
    subst i
    rfl
  · rfl

theorem middle (i:ℤ) (lower:0≤ i) (upper:i≤(n:ℤ)) :
    reference T p i=p ⟨i.toNat,by omega⟩ := by
  unfold reference
  split_ifs with hleft hright
  · have zero:i=0 := by omega
    subst i
    exact zero T _
  · have same:i=(n:ℤ) := by omega
    subst i
    simpa only [sub_self,Int.toNat_natCast] using zero T (p ⟨n,Nat.lt_succ_self n⟩)
  · rfl

theorem prefix_agreement (j:Fin (n+1)) : reference T p (j.val:ℤ)=p j := by
  simpa only [Int.toNat_natCast] using middle T p (j.val:ℤ) (by omega) (by omega)

theorem step_bound (ε:ℝ) (positive:0<ε)
    (pseudo:∀j:ℕ,∀hj:j<n,
      dist (T (p ⟨j+1,by omega⟩)) (p ⟨j,by omega⟩)<ε) :
    ∀i:ℤ,dist (T (reference T p (i+1))) (reference T p i)<ε := by
  intro i
  by_cases hleft : i < 0
  · rw [nonpositive T p (i+1) (by omega),nonpositive T p i (by omega),step]
    simpa only [dist_self] using positive
  by_cases hright : (n:ℤ) ≤ i
  · rw [above T p (i+1) (by omega),above T p i hright]
    have index:i+1-(n:ℤ)=(i-(n:ℤ))+1 := by omega
    rw [index,step]
    simpa only [dist_self] using positive
  · rw [middle T p (i+1) (by omega) (by omega),middle T p i (by omega) (by omega)]
    have successor:(i+1).toNat=i.toNat+1 := by omega
    simpa only [successor] using pseudo i.toNat (by omega)

end LeanShared.FinitePseudoOrbitExtension
