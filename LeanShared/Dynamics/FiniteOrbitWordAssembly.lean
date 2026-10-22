module
public import LeanShared.Dynamics.FinitePseudoOrbitConcatenation
public import LeanShared.Dynamics.EntireOrbitIdentity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Uniform short transition chains assemble arbitrarily many prescribed
actual orbit segments into one finite pseudo-orbit, without increasing the
error. All segment starting times are explicit cumulative lengths. -/
public noncomputable section
namespace LeanShared.FiniteOrbitWordAssembly
open BilateralHomeomorphismOrbit
open scoped BigOperators

@[expose] def offset (gap:ℕ) (length:ℕ→ℕ) (i:ℕ) : ℕ :=
  (Finset.range i).sum (fun j=>length j+gap)
@[expose] def ending (gap:ℕ) (length:ℕ→ℕ) (k:ℕ) : ℕ := offset gap length k+length k

theorem offset_succ (gap:ℕ) (length:ℕ→ℕ) (k:ℕ) :
    offset gap length (k+1)=ending gap length k+gap := by
  simp only [offset,ending,Finset.sum_range_succ]
  omega

theorem ending_succ (gap:ℕ) (length:ℕ→ℕ) (k:ℕ) :
    ending gap length (k+1)=ending gap length k+gap+length (k+1) := by
  rw [ending,offset_succ]

theorem end_le (gap:ℕ) (length:ℕ→ℕ) {i k:ℕ} (hi:i≤k) :
    offset gap length i+length i≤ending gap length k := by
  induction k with
  | zero =>
    have same:i=0 := by omega
    subst i
    exact le_rfl
  | succ k ih =>
    by_cases lower:i≤k
    · exact (ih lower).trans (by rw [ending_succ]; omega)
    · have same:i=k+1 := by omega
      subst i
      exact le_rfl

variable {X:Type*} [MetricSpace X] (T:X≃ₜX) (ε:ℝ) (positive:0<ε)
  (gap:ℕ) (positiveGap:0<gap)
  (chains:∀x y:X,∃p:Fin (gap+1)→X,
    p ⟨0,by omega⟩=x ∧ p ⟨gap,by omega⟩=y ∧
    ∀j:ℕ,∀hj:j<gap,dist (T (p ⟨j+1,by omega⟩)) (p ⟨j,by omega⟩)<ε)

include positive positiveGap chains

set_option maxHeartbeats 1600000 in
theorem assemble (length:ℕ→ℕ) (points:ℕ→X) (k:ℕ) :
    ∃p:Fin (ending gap length k+1)→X,
      (∀i:ℕ,∀hi:i≤k,∀j:ℕ,∀hj:j≤length i,
        p ⟨offset gap length i+j,by have:=end_le gap length hi; omega⟩=orbit T (points i) (j:ℤ)) ∧
      ∀j:ℕ,∀hj:j<ending gap length k,
        dist (T (p ⟨j+1,by omega⟩)) (p ⟨j,by omega⟩)<ε := by
  induction k with
  | zero =>
    refine ⟨fun j=>orbit T (points 0) (j.val:ℤ),?_,?_⟩
    · intro i hi j hj
      have same:i=0 := by omega
      subst i
      simp only [offset,Finset.range_zero,Finset.sum_empty,Nat.zero_add]
    · intro j hj
      have successor:((j+1:ℕ):ℤ)=(j:ℤ)+1 := by omega
      change dist (T (orbit T (points 0) ((j+1:ℕ):ℤ))) (orbit T (points 0) (j:ℤ))<ε
      rw [successor,step,dist_self]
      exact positive
  | succ k ih =>
    obtain ⟨a,trace,aStep⟩ := ih
    let b:Fin (length (k+1)+1)→X:=fun j=>orbit T (points (k+1)) (j.val:ℤ)
    have bStep (j:ℕ) (_hj:j<length (k+1)) :
        dist (T (b ⟨j+1,by omega⟩)) (b ⟨j,by omega⟩)<ε := by
      have successor:((j+1:ℕ):ℤ)=(j:ℤ)+1 := by omega
      change dist (T (orbit T (points (k+1)) ((j+1:ℕ):ℤ))) (orbit T (points (k+1)) (j:ℤ))<ε
      rw [successor,step,dist_self]
      exact positive
    obtain ⟨bridge,first,last,bridgeStep⟩ := chains (a ⟨ending gap length k,by omega⟩) (b ⟨0,by omega⟩)
    let raw:=FinitePseudoOrbitConcatenation.word a b bridge
    have size:ending gap length (k+1)+1=ending gap length k+gap+length (k+1)+1 :=
      congrArg (fun q:ℕ=>q+1) (ending_succ gap length k)
    let p:Fin (ending gap length (k+1)+1)→X:=fun j=>raw (Fin.cast size j)
    refine ⟨p,?_,?_⟩
    · intro i hi j hj
      by_cases lower:i≤k
      · have bound:offset gap length i+j≤ending gap length k :=
          (Nat.add_le_add_left hj _).trans (end_le gap length lower)
        have value := FinitePseudoOrbitConcatenation.left_index a b bridge
          (Fin.cast size ⟨offset gap length i+j,by have:=end_le gap length hi; omega⟩) bound
        exact value.trans (trace i lower j hj)
      · have same:i=k+1 := by omega
        subst i
        have bound:ending gap length k+gap≤offset gap length (k+1)+j := by rw [offset_succ]; omega
        have value := FinitePseudoOrbitConcatenation.right_index a b bridge positiveGap
          (Fin.cast size ⟨offset gap length (k+1)+j,by have:=end_le gap length hi; omega⟩) bound
        have index:offset gap length (k+1)+j-ending gap length k-gap=j := by rw [offset_succ]; omega
        apply value.trans
        change b _=b (⟨j,by omega⟩:Fin (length (k+1)+1))
        exact congrArg b (Fin.ext index)
    · intro j hj
      exact FinitePseudoOrbitConcatenation.step_bound a b bridge T positiveGap first last ε
        aStep bStep bridgeStep j (by rw [←ending_succ]; exact hj)

end LeanShared.FiniteOrbitWordAssembly
