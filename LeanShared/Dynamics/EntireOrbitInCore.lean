module
public import LeanShared.Dynamics.EntireOrbitIdentity
public import LeanShared.Dynamics.IsolatingNeighborhood

/-! Every point of an actual entire orbit contained in a set lies in its
literal isolated core. -/
public section
namespace LeanShared.BilateralHomeomorphismOrbit
open Set
variable {X:Type*} [TopologicalSpace X]

theorem mem_isolatedCore (T:X≃ₜX) (K:Set X) (p:ℤ→X)
    (step:∀n,T (p (n+1))=p n) (inside:∀n,p n∈K) (n:ℤ) :
    p n∈isolatedCore T K := by
  let q:=fun j:ℤ=>p (n+j)
  have qStep (j:ℤ) : T (q (j+1))=q j := by
    simpa only [q,←add_assoc] using step (n+j)
  have canonical := eq_canonical T q qStep
  have initial : q 0=p n := by simp only [q,add_zero]
  constructor
  · intro j
    have identity := congrFun canonical (-(j:ℤ))
    rw [neg_nat_time,initial] at identity
    exact identity ▸ inside (n+(-(j:ℤ)))
  · intro j
    have identity := congrFun canonical (j:ℤ)
    rw [nat_time,initial] at identity
    exact identity ▸ inside (n+(j:ℤ))

end LeanShared.BilateralHomeomorphismOrbit
