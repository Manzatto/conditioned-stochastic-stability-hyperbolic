module
public import LeanShared.Dynamics.BackwardBlockUnrolling
public import Lean.Elab.Tactic.Omega

/-! Sampling a genuine one-step backward orbit gives the exact reversed
finite-word orbit, and unrolling those samples recovers the original path. -/
public noncomputable section
namespace LeanShared.BackwardBlockSampling
open FiniteJetComposition BackwardBlockUnrolling
variable {X:Type*}

theorem word_at (f:ℕ→X→X) (b:ℕ→X) (step:∀m,f m (b (m+1))=b m)
    (N n:ℕ) : ∀k,k≤N→
      word (block f N n) k (b (N*(n+1)))=b (N*(n+1)-k) := by
  intro k
  induction k with
  | zero=>intro _;rfl
  | succ k ih=>
    intro small
    rw [word,Function.comp_apply,ih (by omega)]
    change f (N*(n+1)-1-k) (b (N*(n+1)-k))=b (N*(n+1)-(k+1))
    have expanded:N*(n+1)=N*n+N:=Nat.mul_succ N n
    have first:N*(n+1)-1-k=N*(n+1)-(k+1):=by omega
    have next:N*(n+1)-k=(N*(n+1)-(k+1))+1:=by omega
    rw [first,next]
    exact step _

theorem sampled_step (f:ℕ→X→X) (b:ℕ→X) (step:∀m,f m (b (m+1))=b m)
    (N n:ℕ) : word (block f N n) N (b (N*(n+1)))=b (N*n) := by
  have result:=word_at f b step N n N le_rfl
  simpa only [Nat.mul_succ,Nat.add_sub_cancel] using result

theorem unroll_sample (f:ℕ→X→X) (b:ℕ→X) (step:∀m,f m (b (m+1))=b m)
    (N:ℕ) (positive:0<N) (m:ℕ) :
    unroll f N (fun n=>b (N*n)) m=b m := by
  rw [unroll,word_at f b step N (m/N) (N-m%N) (Nat.sub_le _ _)]
  have remainder:m%N<N:=Nat.mod_lt m positive
  have decomposition:N*(m/N)+m%N=m:=Nat.div_add_mod m N
  have expanded:N*(m/N+1)=N*(m/N)+N:=Nat.mul_succ N (m/N)
  congr 1
  omega
end LeanShared.BackwardBlockSampling
