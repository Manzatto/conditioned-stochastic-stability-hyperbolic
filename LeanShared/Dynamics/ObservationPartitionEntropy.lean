module

public import LeanShared.Dynamics.FiniteConditionalWord
public import LeanShared.Dynamics.ExpansivePartitionCoding
public import LeanShared.Dynamics.DynamicalPartition
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Identification of the manuscript's word entropies with entropy of
actual finite observations, and their invariant chain comparison. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k l : ℕ}
namespace MeasurablePartition

/-- The measurable word observation over the actual first n iterates. -/
@[expose] def wordObservation (P : MeasurablePartition (X := X) k) (T : X → X)
    (n : ℕ) (x : X) : Fin n → Fin k := fun i => P.label (T^[i.val] x)

theorem wordObservation_measurable (P : MeasurablePartition (X := X) k) (T : X → X)
    (measurable : Measurable T) (n : ℕ) : Measurable (P.wordObservation T n) :=
  measurable_pi_iff.mpr (fun i => P.label_measurable.comp (measurable.iterate i.val))

theorem wordObservation_fiber (P : MeasurablePartition (X := X) k) (T : X → X)
    (n : ℕ) (w : Fin n → Fin k) : (P.wordObservation T n) ⁻¹' {w}=dynamicalAtom P T n w := by
  ext x
  simp only [mem_preimage,mem_singleton_iff,dynamicalAtom,mem_iInter,
    funext_iff,wordObservation,P.label_eq_iff]

theorem wordObservation_entropy (P : MeasurablePartition (X := X) k) (T : X → X)
    (μ : Measure X) (n : ℕ) :
    LeanShared.FiniteObservationEntropy.entropy μ (P.wordObservation T n)=dynamicalEntropy P T μ n := by
  simp only [LeanShared.FiniteObservationEntropy.entropy,wordObservation_fiber,dynamicalEntropy]

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions

namespace LeanShared.FiniteObservationEntropy
variable {X I J : Type*} [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem entropy_comp_measurePreserving (μ : Measure X) (T : X → X)
    (invariant : MeasurePreserving T μ μ) (f : X → I) (measurable : Measurable f) :
    entropy μ (f ∘ T)=entropy μ f := by
  unfold entropy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show (f ∘ T) ⁻¹' {i}=T ⁻¹' (f ⁻¹' {i}) from rfl,
    invariant.measureReal_preimage (((measurableSet_singleton i).preimage measurable).nullMeasurableSet)]

theorem conditional_comp_measurePreserving (μ : Measure X) (T : X → X)
    (invariant : MeasurePreserving T μ μ) (f : X → I) (g : X → J)
    (mf : Measurable f) (mg : Measurable g) :
    conditional μ (f ∘ T) (g ∘ T)=conditional μ f g := by
  have joint := entropy_comp_measurePreserving μ T invariant (fun x => (f x,g x)) (mf.prodMk mg)
  have marginal := entropy_comp_measurePreserving μ T invariant g mg
  change entropy μ (fun x => ((f ∘ T) x,(g ∘ T) x))=entropy μ (fun x => (f x,g x)) at joint
  simp only [conditional,joint,marginal]

/-- The invariant conditional entropy cost grows at most linearly with
the observation horizon; this is an actual chain-rule estimate. -/
theorem conditional_orbit_words_le (μ : Measure X) [IsFiniteMeasure μ] (T : X → X)
    (invariant : MeasurePreserving T μ μ) (f : X → I) (g : X → J)
    (mf : Measurable f) (mg : Measurable g) (n : ℕ) :
    conditional μ (fun x (i : Fin n) => f (T^[i.val] x))
      (fun x (i : Fin n) => g (T^[i.val] x)) ≤ (n : ℝ)*conditional μ f g := by
  have bound := conditional_word_le μ n (fun i : Fin n => f ∘ T^[i.val])
    (fun i : Fin n => g ∘ T^[i.val])
    (fun i => mf.comp (invariant.measurable.iterate i.val))
    (fun i => mg.comp (invariant.measurable.iterate i.val))
  simp only [conditional_comp_measurePreserving μ _ (invariant.iterate _) f g mf mg,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at bound
  exact bound

end LeanShared.FiniteObservationEntropy
