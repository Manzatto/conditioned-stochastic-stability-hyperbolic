module
public import LeanShared.Dynamics.MixingUniformOrbitGluing
public import LeanShared.Dynamics.InvariantCoreHomeomorphism
public import LeanShared.Geometry.DiffeomorphismIterates
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! Literal mixing on a compact invariant set gives one fixed length of
small-error chains between EVERY pair of points. The chains themselves are
constructed from actual orbit pieces, with exact prescribed endpoints. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Function
variable {X:Type*} [MetricSpace X] {T:X≃ₜX} {K:Set X}

set_option maxHeartbeats 800000 in
theorem MixingOn.uniform_chains (mixing:MixingOn T K) (compact:IsCompact K)
    (invariant:T '' K=K) (ε:ℝ) (positive:0<ε) :
    ∃N:ℕ,0<N ∧ ∀x y:K,∃p:Fin (N+1)→K,
      p ⟨0,by omega⟩=x ∧ p ⟨N,by omega⟩=y ∧
      ∀j:ℕ,∀hj:j<N,dist (T (p ⟨j+1,by omega⟩).val) (p ⟨j,by omega⟩).val<ε := by
  classical
  obtain ⟨n,hits⟩ := mixing.uniform_orbit_hits compact ε positive
  let N:=n+2
  let S:=invariantCoreHomeomorphism T K invariant
  have equivariant : Semiconj (Subtype.val:K→X) S T := fun _=>rfl
  have powers (k:ℕ) (z:K) : ((S^k) z).val=((T:X→X)^[k]) z.val := by
    rw [DiffeomorphismIterates.coe_pow]
    exact (equivariant.iterate_right k).eq z
  refine ⟨N,by dsimp [N]; omega,fun x y=>?_⟩
  have Ty : T y.val∈K :=
    (congrArg (fun B:Set X=>T y.val∈B) invariant).mp (mem_image_of_mem T y.property)
  obtain ⟨z,hz,first,last⟩ := hits (n+1) (by omega) (T y.val) Ty x.val x.property
  let zK:K:=⟨z,hz⟩
  let p:Fin (N+1)→K:=fun j=>if j.val=0 then x else if j.val=N then y else (S^(N-1-j.val)) zK
  have big : 2≤N := by dsimp [N]; omega
  have p0 : p ⟨0,by omega⟩=x := by simp [p]
  have pN : p ⟨N,by omega⟩=y := by
    have nonzero:N≠0 := by omega
    simp [p,nonzero]
  have interior (j:ℕ) (lower:0<j) (upper:j<N) :
      p ⟨j,by omega⟩=(S^(N-1-j)) zK := by
    simp [p,Nat.ne_of_gt lower,Nat.ne_of_lt upper]
  refine ⟨p,p0,pN,fun j hj=>?_⟩
  by_cases zero:j=0
  · subst j
    rw [p0,interior 1 (by omega) (by dsimp [N]; omega)]
    have move : T ((S^(N-1-1)) zK).val=((S^(N-1)) zK).val := by
      have index:N-1=(N-1-1)+1 := by simp [N]
      exact (congrArg (fun Q:K≃ₜK=>(Q zK).val) (pow_succ' S (N-1-1))).symm.trans
        (congrArg (fun k=>((S^k) zK).val) index.symm)
    have index:N-1=n+1 := by simp [N]
    rw [move,powers,index]
    exact last
  by_cases final:j+1=N
  · have same : (⟨j+1,by omega⟩:Fin (N+1))=⟨N,by omega⟩ := Fin.ext final
    rw [same,pN,interior j (by omega) hj]
    have index:N-1-j=0 := by omega
    rw [index,pow_zero,Homeomorph.one_apply]
    simpa only [dist_comm] using first
  · rw [interior (j+1) (by omega) (by omega),interior j (by omega) hj]
    have index:N-1-j=(N-1-(j+1))+1 := by omega
    have exactStep : T ((S^(N-1-(j+1))) zK).val=((S^(N-1-j)) zK).val := by
      exact (congrArg (fun Q:K≃ₜK=>(Q zK).val) (pow_succ' S (N-1-(j+1)))).symm.trans
        (congrArg (fun k=>((S^k) zK).val) index.symm)
    rw [exactStep,dist_self]
    exact positive

end LeanShared.HyperbolicBasicSet
