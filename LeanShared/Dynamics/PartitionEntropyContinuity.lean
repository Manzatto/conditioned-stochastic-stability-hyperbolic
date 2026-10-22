module

public import LeanShared.Dynamics.DynamicalPartition
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Finite partition entropy is continuous at invariant probabilities
whose partition boundaries carry no mass. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
private theorem frontier_iInter_subset {I : Type*} [Fintype I] (A : I → Set X) :
    frontier (⋂ i, A i) ⊆ ⋃ i, frontier (A i) := by
  have h := (Finset.univ : Finset I).frontier_biUnion_subset (fun i => (A i)ᶜ)
  simpa only [Finset.mem_univ, iUnion_true, ← compl_iInter, frontier_compl, iInter_true] using h

/-- Null boundaries of the original partition remain null for every
actual finite dynamical atom. -/
theorem MeasurablePartition.dynamicalAtom_frontier_null {k : ℕ}
    (P : MeasurablePartition (X := X) k) (T : X → X) (continuous : Continuous T)
    (μ : Measure X) (invariant : MeasurePreserving T μ μ)
    (boundary : ∀ i, μ (frontier (P.atom i))=0) (n : ℕ) (word : Fin n → Fin k) :
    μ (frontier (dynamicalAtom P T n word))=0 := by
  apply measure_mono_null (frontier_iInter_subset _) (measure_iUnion_null (fun j => ?_))
  apply measure_mono_null ((continuous.iterate j.val).frontier_preimage_subset _)
  rw [(invariant.iterate j.val).measure_preimage (isClosed_frontier.measurableSet.nullMeasurableSet), boundary]

/-- Weak convergence gives convergence of every finite-time dynamical
entropy, including null atoms and time zero. -/
theorem MeasurablePartition.dynamicalEntropy_tendsto {I : Type*} {L : Filter I} {k : ℕ}
    (P : MeasurablePartition (X := X) k) (T : X → X) (continuous : Continuous T)
    (μ : ProbabilityMeasure X) (μs : I → ProbabilityMeasure X)
    (convergence : Tendsto μs L (𝓝 μ))
    (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (boundary : ∀ i, (μ : Measure X) (frontier (P.atom i))=0) (n : ℕ) :
    Tendsto (fun i => dynamicalEntropy P T (μs i : Measure X) n) L
      (𝓝 (dynamicalEntropy P T (μ : Measure X) n)) := by
  apply Tendsto.neg
  apply tendsto_finsetSum
  intro word _
  have masses := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' convergence
    (P.dynamicalAtom_frontier_null T continuous (μ : Measure X) invariant boundary n word)
  have reals := (ENNReal.continuousAt_toReal (measure_ne_top (μ : Measure X) _)).tendsto.comp masses
  exact Real.continuous_mul_log.continuousAt.tendsto.comp reals

end LeanShared.ThermodynamicDefinitions
