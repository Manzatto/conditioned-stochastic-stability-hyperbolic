module

import all LeanShared.Dynamics.DynamicalEntropyProduct
public import LeanShared.Dynamics.DynamicalEntropyProduct
public import LeanShared.Dynamics.ObservationPartitionEntropy
public import LeanShared.Dynamics.FiniteObservationMap

/-! Finite-time product-partition entropy is bounded by the entropies of
the actual marginals for every joint probability, without independence. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {k l : ℕ}
namespace MeasurablePartition

theorem product_label (P : MeasurablePartition (X := X) k)
    (Q : MeasurablePartition (X := Y) l) (z : X × Y) :
    (P.product Q).label z=finProdFinEquiv (P.label z.1,Q.label z.2) := by
  apply ((P.product Q).label_eq_iff z _).mpr
  change z.1 ∈ P.atom (finProdFinEquiv.symm (finProdFinEquiv (P.label z.1,Q.label z.2))).1 ∧
    z.2 ∈ Q.atom (finProdFinEquiv.symm (finProdFinEquiv (P.label z.1,Q.label z.2))).2
  simpa only [Equiv.symm_apply_apply] using And.intro (P.label_mem z.1) (Q.label_mem z.2)

theorem dynamicalEntropy_joint_product_le (P : MeasurablePartition (X := X) k)
    (Q : MeasurablePartition (X := Y) l) (T : X → X) (S : Y → Y)
    (measurableT : Measurable T) (measurableS : Measurable S)
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ] (n : ℕ) :
    dynamicalEntropy (P.product Q) (fun z : X × Y => (T z.1,S z.2)) μ n ≤
      dynamicalEntropy P T (μ.map Prod.fst) n+dynamicalEntropy Q S (μ.map Prod.snd) n := by
  let F := fun z : X × Y => P.wordObservation T n z.1
  let G := fun z : X × Y => Q.wordObservation S n z.2
  have same : (words n k l) ∘ (P.product Q).wordObservation (fun z : X × Y => (T z.1,S z.2)) n =
      fun z => (F z,G z) := by
    funext z
    apply Prod.ext <;> funext i <;>
      simp only [Function.comp_apply,words,Equiv.coe_fn_mk,wordObservation,iterate_product,product_label,Equiv.symm_apply_apply,F,G]
  have joint := LeanShared.FiniteObservationEntropy.entropy_injective μ
    ((P.product Q).wordObservation (fun z : X × Y => (T z.1,S z.2)) n)
    (words n k l) (words n k l).injective
  rw [same] at joint
  have bound := LeanShared.FiniteObservationEntropy.pair_entropy_le μ F G
    ((P.wordObservation_measurable T measurableT n).comp measurable_fst)
    ((Q.wordObservation_measurable S measurableS n).comp measurable_snd)
  rw [joint,(P.product Q).wordObservation_entropy] at bound
  have first := LeanShared.FiniteObservationEntropy.entropy_map μ Prod.fst measurable_fst
    (P.wordObservation T n) (P.wordObservation_measurable T measurableT n)
  have second := LeanShared.FiniteObservationEntropy.entropy_map μ Prod.snd measurable_snd
    (Q.wordObservation S n) (Q.wordObservation_measurable S measurableS n)
  rw [P.wordObservation_entropy] at first
  rw [Q.wordObservation_entropy] at second
  change _ = LeanShared.FiniteObservationEntropy.entropy μ F at first
  change _ = LeanShared.FiniteObservationEntropy.entropy μ G at second
  rw [←first,←second] at bound
  exact bound

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
