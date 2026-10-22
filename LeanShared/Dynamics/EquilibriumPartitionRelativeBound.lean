module

public import LeanShared.Dynamics.BowenPartitionEntropyLower
public import LeanShared.Dynamics.PartitionSingleEntropy
public import LeanShared.Dynamics.FiniteGibbsRelativeBound
public import LeanShared.Dynamics.FiniteObservationIntegral
public import LeanShared.Dynamics.InvariantOrbitEnergy
public import LeanShared.Dynamics.ExpansiveVariationalMaximizer

/-! An ARBITRARY equilibrium probability has uniformly bounded relative
entropy against a Gibbs reference on every actual Bowen-small partition
with fine-ball reference masses. All entropy, energy and free-energy
bounds are derived from the literal equilibrium definition. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

set_option maxHeartbeats 1800000 in
theorem equilibrium_partition_relative_bound {k : ℕ} (Q : MeasurablePartition (X := X) k)
    (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (μ ν : ProbabilityMeasure X) (state : IsEquilibriumState T φ univ μ)
    (P A D : ℝ) (pressureP : pressure T φ univ = (P : EReal)) (positiveA : 0 < A)
    (n : ℕ) (positiveN : 0 < n) (energy : Fin k → ℝ)
    (mesh : ∀ i x y, x ∈ Q.atom i → y ∈ Q.atom i →
      ∀ j < n, dist (T^[j] x) (T^[j] y) ≤ c)
    (distortion : ∀ i x, x ∈ Q.atom i → orbitSum T φ n x - D ≤ energy i)
    (reference : ∀ i, ENNReal.ofReal (A * Real.exp (energy i - (n : ℝ) * P)) ≤
      (ν : Measure X) (Q.atom i)) :
    (∑ i, (μ : Measure X).real (Q.atom i) * Real.log
      ((μ : Measure X).real (Q.atom i) / (ν : Measure X).real (Q.atom i))) ≤ D - Real.log A := by
  have invariant : MeasurePreserving T (μ : Measure X) μ := ⟨state.1, state.2.1⟩
  have entropyLower := bowen_partition_entropy_lower Q T c positiveC expansive μ invariant n positiveN mesh
  rw [Q.dynamicalEntropy_one] at entropyLower
  have referenceReal (i : Fin k) : A * Real.exp (energy i - (n : ℝ) * P) ≤
      (ν : Measure X).real (Q.atom i) := by
    have bound := ENNReal.toReal_mono (measure_ne_top (ν : Measure X) (Q.atom i)) (reference i)
    rw [ENNReal.toReal_ofReal (mul_nonneg positiveA.le (Real.exp_nonneg _))] at bound
    exact bound
  have intEnergy : Integrable (fun x => energy (Q.label x)) (μ : Measure X) :=
    Integrable.comp_measurable (f := Q.label) (g := energy) Integrable.of_finite Q.label_measurable
  have energyLower := integral_mono_ae
    ((integrable_orbitSum T T.continuous (μ : Measure X) φ n).sub (integrable_const D))
    intEnergy (Filter.Eventually.of_forall (fun x => distortion (Q.label x) x (Q.label_mem x)))
  change (∫ x, orbitSum T φ n x - D ∂(μ : Measure X)) ≤
    ∫ x, energy (Q.label x) ∂(μ : Measure X) at energyLower
  rw [integral_sub (integrable_orbitSum T T.continuous (μ : Measure X) φ n) (integrable_const D),
    integral_orbitSum_invariant T (μ : Measure X) invariant φ n,
    LeanShared.FiniteObservationEntropy.integral_observation (μ : Measure X) Q.label Q.label_measurable energy] at energyLower
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
    one_mul, Q.label_fiber] at energyLower
  obtain ⟨H, finiteH⟩ := entropy_finite_of_expansive T c positiveC expansive μ invariant
  have freeEnergy := state.2.2.2.2
  rw [finiteH, ← EReal.coe_add, pressureP] at freeEnergy
  have numeric := EReal.coe_injective freeEnergy
  have scaled : (n : ℝ) * (entropy T (μ : Measure X)).toReal +
      (n : ℝ) * (∫ x, φ x ∂(μ : Measure X)) = (n : ℝ) * P := by
    rw [finiteH, EReal.toReal_coe]
    nlinarith
  exact LeanShared.FiniteRelativeEntropy.bound_of_gibbs_and_free_energy
    (fun i => (μ : Measure X).real (Q.atom i)) (fun i => (ν : Measure X).real (Q.atom i))
    energy A n P ((n : ℝ) * (entropy T (μ : Measure X)).toReal)
    ((n : ℝ) * (∫ x, φ x ∂(μ : Measure X))) D
    (fun _ => measureReal_nonneg) (Q.atom_masses_total (μ : Measure X)) positiveA
    referenceReal entropyLower energyLower scaled

end LeanShared.ThermodynamicDefinitions
