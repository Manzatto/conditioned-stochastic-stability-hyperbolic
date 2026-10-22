module
public import LeanShared.Analysis.BoundedFiniteJetSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A smooth compact family with actual finite derivative controls lifts
to the complete compatible jet graph, with the same uniform and Holder
bounds. The lift is fixed by its physical function. -/
public noncomputable section
open Set
open scoped ContDiff
namespace LeanShared.BoundedFiniteJetSpace
universe u
variable {E F:Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] [CompleteSpace F]

theorem lift_family {X:Type*} [PseudoMetricSpace X] (n:ℕ) (f:X→E→F)
    (smooth:∀p,ContDiff ℝ ∞ (f p)) (compact:∀p,HasCompactSupport (f p))
    {B H a:ℝ} (hB:0≤B) (hH:0≤H)
    (value:∀p,∀j≤n,∀x,‖iteratedFDeriv ℝ j (f p) x‖≤B)
    (holder:∀p q,∀j≤n,∀x,‖iteratedFDeriv ℝ j (f p) x-
      iteratedFDeriv ℝ j (f q) x‖≤H*dist p q^a):
    ∃v:X→(construct (E:=E) n (F:=F)).carrier,
      (∀p x,(construct n (F:=F)).physical (v p) x=f p x) ∧
      (∀p,‖v p‖≤B) ∧ ∀p q,‖v p-v q‖≤H*dist p q^a:=by
  let d:=construct (E:=E) n (F:=F)
  choose v rep using fun p=>d.represents (f p) (smooth p) (compact p)
  have physical (p:X):(d.physical (v p):E→F)=f p:=funext (rep p)
  refine ⟨v,rep,?_,?_⟩
  · intro p
    apply norm_le n (v p) B hB
    intro j hj x
    rw [physical p]
    exact value p j hj x
  · intro p q
    apply norm_le n (v p-v q) (H*dist p q^a) (by positivity)
    intro j hj x
    have equal:(d.physical (v p-v q):E→F)=f p-f q:=by
      funext y
      rw [map_sub]
      exact congrArg₂ (fun u v:F=>u-v) (rep p y) (rep q y)
    rw [equal,iteratedFDeriv_sub_apply ((smooth p).of_le (by simp)).contDiffAt
      ((smooth q).of_le (by simp)).contDiffAt]
    exact holder p q j hj x
end LeanShared.BoundedFiniteJetSpace
