module

public import LeanShared.Dynamics.FiniteConditionalObservation
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-! The conditional entropy of actual finite observation words is at
most the sum of the coordinate conditional entropies. -/
public noncomputable section
open Function MeasureTheory
open scoped BigOperators
namespace LeanShared.FiniteObservationEntropy
variable {X I J : Type*} [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace J] [MeasurableSingletonClass J] in
private theorem conditional_equiv {K L : Type*} [Fintype K] [Fintype L]
    (μ : Measure X) (f : X → I) (g : X → J) (e : I ≃ K) (d : J ≃ L) :
    conditional μ (e ∘ f) (d ∘ g)=conditional μ f g := by
  have joint := entropy_injective μ (fun x => (f x,g x))
    (Equiv.prodCongr e d) (Equiv.prodCongr e d).injective
  have marginal := entropy_injective μ g d d.injective
  change entropy μ (fun x => ((e ∘ f) x,(d ∘ g) x))=entropy μ (fun x => (f x,g x)) at joint
  simp only [conditional,joint,marginal]

theorem conditional_word_le (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ)
    (f : Fin n → X → I) (g : Fin n → X → J)
    (mf : ∀ i, Measurable (f i)) (mg : ∀ i, Measurable (g i)) :
    conditional μ (fun x i => f i x) (fun x i => g i x) ≤
      ∑ i : Fin n, conditional μ (f i) (g i) := by
  induction n with
  | zero =>
    let empty : Fin 0 → I := Fin.elim0
    have same : (fun x (i : Fin 0) => f i x)=(fun _ => empty) := by
      funext x i
      exact Fin.elim0 i
    rw [same]
    have joint := entropy_injective μ (fun x (i : Fin 0) => g i x)
      (fun w => (empty,w)) (fun _ _ equal => congrArg Prod.snd equal)
    change entropy μ (fun x => (empty,fun i : Fin 0 => g i x))=
      entropy μ (fun x (i : Fin 0) => g i x) at joint
    simp only [conditional,joint,sub_self,Fin.sum_univ_zero,le_refl]
  | succ n ih =>
    let F : X → (Fin (n+1) → I) := fun x i => f i x
    let G : X → (Fin (n+1) → J) := fun x i => g i x
    have split := conditional_equiv μ F G (Fin.consEquiv (fun _ : Fin (n+1) => I)).symm
      (Fin.consEquiv (fun _ : Fin (n+1) => J)).symm
    change conditional μ (fun x => (f 0 x,fun i : Fin n => f i.succ x))
      (fun x => (g 0 x,fun i : Fin n => g i.succ x))=conditional μ F G at split
    rw [←split]
    have pair := conditional_pair_le μ (f 0) (g 0)
      (fun x (i : Fin n) => f i.succ x) (fun x (i : Fin n) => g i.succ x)
      (mf 0) (mg 0) (measurable_pi_iff.mpr (fun i => mf i.succ))
      (measurable_pi_iff.mpr (fun i => mg i.succ))
    have tail := ih (fun i => f i.succ) (fun i => g i.succ)
      (fun i => mf i.succ) (fun i => mg i.succ)
    exact pair.trans (by simpa only [Fin.sum_univ_succ] using add_le_add (le_refl (conditional μ (f 0) (g 0))) tail)

end LeanShared.FiniteObservationEntropy
