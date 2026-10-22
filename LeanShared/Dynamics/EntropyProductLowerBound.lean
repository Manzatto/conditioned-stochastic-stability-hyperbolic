module

public import LeanShared.Dynamics.DynamicalEntropyProduct
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! The actual metric entropy of an independent product dominates the sum
of the factor metric entropies. Every finite partition and dynamical
refinement is the literal partition in the entropy definition. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private theorem partition_rate_product {k l : ℕ}
    (P : MeasurablePartition (X := X) k) (Q : MeasurablePartition (X := Y) l)
    (T : X → X) (S : Y → Y) (hT : Measurable T) (hS : Measurable S)
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (liminf (fun n : ℕ => (((n : ℝ)⁻¹*dynamicalEntropy P T μ n : ℝ) : EReal)) atTop)+
      (liminf (fun n : ℕ => (((n : ℝ)⁻¹*dynamicalEntropy Q S ν n : ℝ) : EReal)) atTop) ≤
    liminf (fun n : ℕ => (((n : ℝ)⁻¹*dynamicalEntropy (P.product Q)
      (fun z : X × Y => (T z.1,S z.2)) (μ.prod ν) n : ℝ) : EReal)) atTop := by
  have addition := EReal.le_liminf_add (f := atTop)
    (u := fun n : ℕ => (((n : ℝ)⁻¹*dynamicalEntropy P T μ n : ℝ) : EReal))
    (v := fun n : ℕ => (((n : ℝ)⁻¹*dynamicalEntropy Q S ν n : ℝ) : EReal))
  have identity : (fun n : ℕ =>
      (((n : ℝ)⁻¹*dynamicalEntropy P T μ n : ℝ) : EReal)+
      (((n : ℝ)⁻¹*dynamicalEntropy Q S ν n : ℝ) : EReal)) =
      (fun n : ℕ => (((n : ℝ)⁻¹*dynamicalEntropy (P.product Q)
        (fun z : X × Y => (T z.1,S z.2)) (μ.prod ν) n : ℝ) : EReal)) := by
    funext n
    rw [P.dynamicalEntropy_product Q T S hT hS μ ν n,mul_add,EReal.coe_add]
  exact identity ▸ addition

/-- The product lower entropy bound uses no equilibrium package, pressure
identity or variational inequality. -/
theorem entropy_product_ge (T : X → X) (S : Y → Y) (hT : Measurable T) (hS : Measurable S)
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    entropy T μ+entropy S ν ≤ entropy (fun z : X × Y => (T z.1,S z.2)) (μ.prod ν) := by
  apply EReal.add_le_of_forall_lt
  intro a ha b hb
  obtain ⟨k,hk⟩ := lt_iSup_iff.mp ha
  obtain ⟨P,hP⟩ := lt_iSup_iff.mp hk
  obtain ⟨l,hl⟩ := lt_iSup_iff.mp hb
  obtain ⟨Q,hQ⟩ := lt_iSup_iff.mp hl
  exact (add_le_add hP.le hQ.le).trans ((partition_rate_product P Q T S hT hS μ ν).trans
    (le_iSup_of_le (k*l) (le_iSup_of_le (P.product Q) le_rfl)))

end LeanShared.ThermodynamicDefinitions
