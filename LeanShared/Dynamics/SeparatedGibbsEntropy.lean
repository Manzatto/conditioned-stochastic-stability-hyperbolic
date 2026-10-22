module

public import LeanShared.Dynamics.FiniteAtomicEntropy
import all LeanShared.Dynamics.FiniteAtomicProbability
public import LeanShared.Dynamics.ObservationPartitionEntropy
public import LeanShared.Dynamics.ThermodynamicDefinitions

/-! Exact finite entropy-plus-orbit-energy identity for actual Gibbs
probabilities on separated orbit sets. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
namespace MeasurablePartition

/-- A separated set's Gibbs weights give an actual probability with
entropy plus energy exactly the logarithm of its weighted partition sum. -/
theorem separated_gibbs_identity (P : MeasurablePartition (X := X) k)
    (T : X → X) (φ : X → ℝ) (K : Set X) (n : ℕ) (ε : ℝ)
    (s : Finset X) (nonempty : s.Nonempty) (separated : Separated T K n ε s)
    (mesh : ∀ i x y, x ∈ P.atom i → y ∈ P.atom i → dist x y < ε) :
    let a : s → ℝ := fun x => orbitSum T φ n x.val
    let : Nonempty s := nonempty.to_subtype
    let σ := LeanShared.FiniteAtomicProbability.gibbs a Subtype.val
    dynamicalEntropy P T (σ : Measure X) n + (∫ x, orbitSum T φ n x ∂(σ : Measure X)) =
      Real.log (∑ x ∈ s, Real.exp (orbitSum T φ n x)) := by
  let a : s → ℝ := fun x => orbitSum T φ n x.val
  let : Nonempty s := nonempty.to_subtype
  have distinguishes : Injective (P.wordObservation T n ∘ (Subtype.val : s → X)) := by
    intro x y equal
    apply Subtype.ext
    by_contra different
    obtain ⟨j,hj,far⟩ := separated.2 x.val x.property y.val y.property different
    have names := congrFun equal ⟨j,hj⟩
    have near := mesh _ _ _ (P.label_mem (T^[j] x.val))
      ((P.label_eq_iff _ _).mp names.symm)
    exact not_lt_of_ge far near
  have entropy := LeanShared.FiniteAtomicProbability.observation_entropy_of_injective
    (LeanShared.FiniteGibbsOptimizer.weights a) Subtype.val
    (fun i => (LeanShared.FiniteGibbsOptimizer.weights_positive a i).le)
    (P.wordObservation T n) distinguishes
  change LeanShared.FiniteObservationEntropy.entropy
    (LeanShared.FiniteAtomicProbability.gibbs a Subtype.val : Measure X) (P.wordObservation T n)=_ at entropy
  have energy := LeanShared.FiniteAtomicProbability.gibbs_integral a Subtype.val (orbitSum T φ n)
  have identity := LeanShared.FiniteGibbsOptimizer.value_weights a
  dsimp only [LeanShared.FiniteGibbsOptimizer.value,LeanShared.FiniteGibbsOptimizer.partition] at identity
  change dynamicalEntropy P T (LeanShared.FiniteAtomicProbability.gibbs a Subtype.val : Measure X) n +
    (∫ x, orbitSum T φ n x ∂(LeanShared.FiniteAtomicProbability.gibbs a Subtype.val : Measure X)) = _
  rw [←P.wordObservation_entropy T,entropy,energy]
  have partition_eq : (∑ x : s, Real.exp (a x))=
      ∑ x ∈ s, Real.exp (orbitSum T φ n x) := Finset.sum_coe_sort s (fun x : X => Real.exp (orbitSum T φ n x))
  rw [partition_eq] at identity
  exact identity

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
