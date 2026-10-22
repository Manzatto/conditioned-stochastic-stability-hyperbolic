module

public import LeanShared.Dynamics.SeparatedGibbsBlockEstimate
public import LeanShared.Dynamics.SmallBoundaryPartition
public import LeanShared.Dynamics.PartitionEntropyRate

/-! Weak limits of actual separated Gibbs Cesaro probabilities bound the
normalized separated partition sums by their invariant entropy and energy. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

@[expose] def separatedGibbsProbability (T : X → X) (φ : X →ᵇ ℝ)
    (n : ℕ) (s : Finset X) (nonempty : s.Nonempty) : ProbabilityMeasure X :=
  let : Nonempty s := nonempty.to_subtype
  LeanShared.FiniteAtomicProbability.gibbs
    (fun x : s => orbitSum T φ (n+1) x.val) Subtype.val

variable [CompactSpace X]

theorem separated_gibbs_limit (T : X → X) (continuous : Continuous T)
    (φ : X →ᵇ ℝ) (K : Set X) (ε : ℝ) (positive : 0 < ε)
    (s : ℕ → Finset X) (nonempty : ∀ n, (s n).Nonempty)
    (separated : ∀ n, Separated T K (n+1) ε (s n))
    (ι : ℕ → ℕ) (mono : StrictMono ι) (ν : ProbabilityMeasure X) (L : ℝ)
    (weak : Tendsto (fun j => LeanShared.CesaroProbability.probabilityMeasure T
      (separatedGibbsProbability T φ (ι j) (s (ι j)) (nonempty (ι j))) (ι j)) atTop (𝓝 ν))
    (sums : Tendsto (fun j => Real.log (∑ x ∈ s (ι j),
      Real.exp (orbitSum T φ (ι j+1) x))/(ι j+1 : ℝ)) atTop (𝓝 L)) :
    MeasurePreserving T (ν : Measure X) (ν : Measure X) ∧
      ∃ (k : ℕ) (P : MeasurablePartition (X := X) k),
        L ≤ P.entropyRate T (ν : Measure X) + ∫ x, φ x ∂(ν : Measure X) := by
  let σ (n : ℕ) := separatedGibbsProbability T φ n (s n) (nonempty n)
  have invariant := LeanShared.CesaroProbability.invariant_of_limit T continuous σ ν ι mono weak
  obtain ⟨k,P,boundary,mesh⟩ := exists_small_boundary_partition (ν : Measure X) ε positive
  refine ⟨invariant,k,P,?_⟩
  have finite_bound (m : ℕ) (hm : 0 < m) :
      L ≤ dynamicalEntropy P T (ν : Measure X) m/m + ∫ x, φ x ∂(ν : Measure X) := by
    have ent := (P.dynamicalEntropy_tendsto T continuous ν _ weak invariant boundary m).div_const (m : ℝ)
    have energy := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp weak) φ
    have vanish : Tendsto (fun j => (2*(m : ℝ)*Real.log (k : ℝ))/(ι j+1 : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, one_mul, Function.comp_def] using
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp mono.tendsto_atTop).const_mul
          (2*(m : ℝ)*Real.log (k : ℝ))
    have upper := (ent.add energy).add vanish
    simp only [add_zero] at upper
    apply le_of_tendsto_of_tendsto sums upper
    filter_upwards [mono.tendsto_atTop.eventually (eventually_ge_atTop m)] with j hj
    exact P.separated_gibbs_block_estimate T continuous φ K (ι j) ε (s (ι j))
      (nonempty (ι j)) (separated (ι j)) mesh m hm (by omega)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    ((P.entropyRate_tendsto T (ν : Measure X) invariant).add_const (∫ x, φ x ∂(ν : Measure X)))
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact finite_bound m hm

end LeanShared.ThermodynamicDefinitions
