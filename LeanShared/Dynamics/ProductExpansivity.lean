module

import all LeanShared.Dynamics.DynamicalEntropyProduct
public import LeanShared.Dynamics.DynamicalEntropyProduct
public import Mathlib.Topology.Homeomorph.Lemmas

/-! Products preserve the actual two-sided metric expansivity predicate. -/
public noncomputable section
open Set Function
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem product_expansivity (T : X ≃ₜ X) (S : Y ≃ₜ Y) (c d : ℝ)
    (expansiveT : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (expansiveS : ∀ x y, (∀ n : ℕ,
      dist ((S : Y → Y)^[n] x) ((S : Y → Y)^[n] y) ≤ d ∧
      dist ((S.symm : Y → Y)^[n] x) ((S.symm : Y → Y)^[n] y) ≤ d) → x=y) :
    ∀ x y : X × Y, (∀ j : ℕ,
      dist (((T.prodCongr S) : X × Y → X × Y)^[j] x) (((T.prodCongr S) : X × Y → X × Y)^[j] y) ≤ min c d ∧
      dist ((((T.prodCongr S).symm) : X × Y → X × Y)^[j] x) ((((T.prodCongr S).symm) : X × Y → X × Y)^[j] y) ≤ min c d) → x=y := by
  let TX := T.prodCongr S
  change ∀ x y : X × Y, (∀ j : ℕ,
      dist ((TX : X × Y → X × Y)^[j] x) ((TX : X × Y → X × Y)^[j] y) ≤ min c d ∧
      dist ((TX.symm : X × Y → X × Y)^[j] x) ((TX.symm : X × Y → X × Y)^[j] y) ≤ min c d) → x=y
  intro x y small
  apply Prod.ext
  · apply expansiveT
    intro j
    have h := small j
    change dist ((fun z : X × Y => (T z.1,S z.2))^[j] x)
      ((fun z : X × Y => (T z.1,S z.2))^[j] y) ≤ _ ∧
      dist ((fun z : X × Y => (T.symm z.1,S.symm z.2))^[j] x)
      ((fun z : X × Y => (T.symm z.1,S.symm z.2))^[j] y) ≤ _ at h
    simp only [MeasurablePartition.iterate_product,Prod.dist_eq,max_le_iff] at h
    exact ⟨h.1.1.trans (min_le_left c d),h.2.1.trans (min_le_left c d)⟩
  · apply expansiveS
    intro j
    have h := small j
    change dist ((fun z : X × Y => (T z.1,S z.2))^[j] x)
      ((fun z : X × Y => (T z.1,S z.2))^[j] y) ≤ _ ∧
      dist ((fun z : X × Y => (T.symm z.1,S.symm z.2))^[j] x)
      ((fun z : X × Y => (T.symm z.1,S.symm z.2))^[j] y) ≤ _ at h
    simp only [MeasurablePartition.iterate_product,Prod.dist_eq,max_le_iff] at h
    exact ⟨h.1.2.trans (min_le_right c d),h.2.2.trans (min_le_right c d)⟩
end LeanShared.ThermodynamicDefinitions
