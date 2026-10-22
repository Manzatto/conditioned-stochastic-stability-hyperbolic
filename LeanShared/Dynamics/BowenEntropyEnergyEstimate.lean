module

public import LeanShared.Dynamics.OrbitPartitionEntropyComparison
public import LeanShared.Dynamics.BowenCoverPartition
public import LeanShared.Dynamics.FiniteObservationGibbsEnergy
public import LeanShared.Dynamics.InvariantOrbitEnergy
public import LeanShared.Dynamics.ExpansiveSeparatedCardinality
public import LeanShared.Dynamics.SeparatedPartitionFiniteness
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! Actual finite partition free energy is bounded by the actual weighted
Bowen separated supremum, with an arbitrarily small per-iterate error. -/
public noncomputable section
open Set Function MeasureTheory Metric
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ}
namespace MeasurablePartition

theorem exists_bowen_entropy_energy_bound (P : MeasurablePartition (X := X) k)
    (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (μ : ProbabilityMeasure X) (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (φ : X →ᵇ ℝ) (η : ℝ) (ηpositive : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 0 < n →
      dynamicalEntropy P T (μ : Measure X) n/n + (∫ x, φ x ∂(μ : Measure X)) ≤
        Real.log (separatedPartitionSum T φ univ n ε).toReal/n + 2*η := by
  classical
  let : Nonempty X := nonempty_of_isProbabilityMeasure (μ : Measure X)
  obtain ⟨δ,δpositive,entropyBound⟩ := P.exists_orbit_partition_entropy_bound T μ invariant η ηpositive
  obtain ⟨d,dpositive,oscillation⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous φ.continuous) η ηpositive
  let ε := min δ d/4
  have εpositive : 0 < ε := div_pos (lt_min δpositive dpositive) (by norm_num)
  obtain ⟨a,_,counts⟩ := LeanShared.FiniteExpansiveWords.exists_uniform_card_bound T c positive expansive
  obtain ⟨p,count⟩ := counts ε εpositive
  refine ⟨ε,εpositive,?_⟩
  intro n npositive
  obtain ⟨l,Q,center,lpositive,injective,separated,close⟩ :=
    exists_bowen_cover_partition T T.continuous n ε εpositive (a^(n+p)) (count n)
  let : Nonempty (Fin l) := ⟨⟨0,lpositive⟩⟩
  have mesh (i) (x y : X) (hx : x ∈ Q.atom i) (hy : y ∈ Q.atom i) (j) (hj : j < n) :
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) < δ := by
    have first := close i x hx j hj
    have second := close i y hy j hj
    have triangle := dist_triangle ((T : X → X)^[j] x) ((T : X → X)^[j] (center i)) ((T : X → X)^[j] y)
    rw [dist_comm ((T : X → X)^[j] (center i))] at triangle
    have εδ : ε ≤ δ/4 := div_le_div_of_nonneg_right (min_le_left δ d) (by norm_num)
    linarith
  have ent := entropyBound n npositive l Q mesh
  have energyPointwise (x : X) : orbitSum T φ n x ≤ orbitSum T φ n (center (Q.label x))+(n : ℝ)*η := by
    have each (j : ℕ) (hj : j ∈ Finset.range n) :
        φ ((T : X → X)^[j] x) ≤ φ ((T : X → X)^[j] (center (Q.label x)))+η := by
      have near := close (Q.label x) x (Q.label_mem x) j (Finset.mem_range.mp hj)
      have εd : ε ≤ d/4 := div_le_div_of_nonneg_right (min_le_right δ d) (by norm_num)
      have osc := oscillation (by linarith : dist ((T : X → X)^[j] x)
        ((T : X → X)^[j] (center (Q.label x))) < d)
      rw [Real.dist_eq] at osc
      linarith [(le_abs_self (φ ((T : X → X)^[j] x)-φ ((T : X → X)^[j] (center (Q.label x)))))]
    have sumBound := Finset.sum_le_sum each
    simpa only [orbitSum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using sumBound
  have gibbs := LeanShared.FiniteObservationEntropy.entropy_integral_le_log_partition (μ : Measure X)
    Q.label Q.label_measurable (fun i => orbitSum T φ n (center i)) (orbitSum T φ n)
    (integrable_orbitSum T T.continuous (μ : Measure X) φ n) ((n : ℝ)*η) energyPointwise
  rw [integral_orbitSum_invariant T (μ : Measure X) invariant φ n] at gibbs
  have finite := (partitionSum_positive_finite_of_count T φ n p a ε (count n)).2
  have zBound : ENNReal.ofReal (∑ i : Fin l, Real.exp (orbitSum T φ n (center i))) ≤
      separatedPartitionSum T φ univ n ε := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    have upper : (∑ x ∈ Finset.univ.image center, ENNReal.ofReal (Real.exp (orbitSum T φ n x))) ≤
        separatedPartitionSum T φ univ n ε := by
      unfold separatedPartitionSum
      exact le_iSup_of_le _ (le_iSup_of_le separated le_rfl)
    simpa only [Finset.sum_image (fun _ _ _ _ h => injective h)] using upper
  have realBound := ENNReal.toReal_mono finite zBound
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))] at realBound
  have logBound := Real.log_le_log (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty) realBound
  have npos : (0 : ℝ) < n := by exact_mod_cast npositive
  have combined : dynamicalEntropy P T (μ : Measure X) n + (n : ℝ)*(∫ x, φ x ∂(μ : Measure X)) ≤
      Real.log (separatedPartitionSum T φ univ n ε).toReal + 2*(n : ℝ)*η := by linarith
  nlinarith [div_mul_cancel₀ (dynamicalEntropy P T (μ : Measure X) n) npos.ne',
    div_mul_cancel₀ (Real.log (separatedPartitionSum T φ univ n ε).toReal) npos.ne']

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
