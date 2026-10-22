module

public import LeanShared.Dynamics.SeparatedGibbsLimit
public import LeanShared.Dynamics.CompactInvariantProbability

/-! Actual maximizing subsequences of separated Gibbs partition sums have
invariant probability limits whose finite-partition free energy dominates them. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

theorem separated_gibbs_compact_limit (T : X → X) (continuous : Continuous T)
    (φ : X →ᵇ ℝ) (K : Set X) (ε : ℝ) (positive : 0 < ε)
    (s : ℕ → Finset X) (nonempty : ∀ n, (s n).Nonempty)
    (separated : ∀ n, Separated T K (n+1) ε (s n))
    (above : BddAbove (range (fun n => Real.log (∑ x ∈ s n,
      Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ))))
    (below : BddBelow (range (fun n => Real.log (∑ x ∈ s n,
      Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ)))) :
    ∃ ν : ProbabilityMeasure X, MeasurePreserving T (ν : Measure X) (ν : Measure X) ∧
      ∃ (k : ℕ) (P : MeasurablePartition (X := X) k),
        limsup (fun n => Real.log (∑ x ∈ s n, Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ)) atTop ≤
          P.entropyRate T (ν : Measure X) + ∫ x, φ x ∂(ν : Measure X) := by
  let f (n : ℕ) := Real.log (∑ x ∈ s n, Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ)
  obtain ⟨a,limit,escape⟩ := exists_seq_tendsto_limsup
    (f := atTop) (u := f)
    (below.isBoundedUnder_of_range (f := atTop)).isCoboundedUnder_le
    (above.isBoundedUnder_of_range (f := atTop))
  obtain ⟨b,monob,monoab⟩ := strictMono_subseq_of_tendsto_atTop escape
  let σ (n : ℕ) := separatedGibbsProbability T φ n (s n) (nonempty n)
  let bar (n : ℕ) := LeanShared.CesaroProbability.probabilityMeasure T (σ n) n
  obtain ⟨ν,_,c,monoc,weak⟩ := isSeqCompact_univ (fun j => mem_univ (bar (a (b j))))
  have mono : StrictMono (a ∘ b ∘ c) := monoab.comp monoc
  have sums := (limit.comp monob.tendsto_atTop).comp monoc.tendsto_atTop
  have result := separated_gibbs_limit T continuous φ K ε positive s nonempty separated
    (a ∘ b ∘ c) mono ν (limsup f atTop) weak sums
  exact ⟨ν,result⟩

end LeanShared.ThermodynamicDefinitions
