module

public import LeanShared.Dynamics.SeparatedGibbsCompactLimit
public import LeanShared.Dynamics.SeparatedGibbsSumBounds
public import LeanShared.Dynamics.ExpansiveVariationalMaximizer
public import LeanShared.Dynamics.ExpansiveSeparatedCardinality

/-! Every actual separated Gibbs partition-sum sequence on a compact
expansive system is bounded by the free energy of an actual invariant law.
No invariant limit, scalar bound, or equilibrium is supplied as an input. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

 theorem expansive_gibbs_free_energy [Nonempty X]
    (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (φ : X →ᵇ ℝ) (ε : ℝ) (εpositive : 0 < ε)
    (s : ℕ → Finset X) (nonempty : ∀ n, (s n).Nonempty)
    (separated : ∀ n, Separated T univ (n+1) ε (s n)) :
    ∃ ν : ProbabilityMeasure X, MeasurePreserving T (ν : Measure X) (ν : Measure X) ∧
      limsup (fun n => Real.log (∑ x ∈ s n, Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ)) atTop ≤
        (entropy T (ν : Measure X)).toReal + ∫ x, φ x ∂(ν : Measure X) := by
  obtain ⟨a,apos,counts⟩ := LeanShared.FiniteExpansiveWords.exists_uniform_card_bound T c positive expansive
  obtain ⟨p,count⟩ := counts ε εpositive
  have bound (n : ℕ) := normalized_gibbs_sum_bounds T φ n (s n) (nonempty n) a apos p
    ((count (n+1) (s n) (separated n)).trans
      (Nat.pow_le_pow_right (by omega) (by nlinarith : n+1+p ≤ (n+1)*(p+1))))
  have above : BddAbove (range (fun n => Real.log (∑ x ∈ s n,
      Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ))) := by
    refine ⟨(p+1 : ℝ)*Real.log (a : ℝ)+‖φ‖,?_⟩
    rintro y ⟨n,rfl⟩
    exact (bound n).2
  have below : BddBelow (range (fun n => Real.log (∑ x ∈ s n,
      Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ))) := by
    refine ⟨-‖φ‖,?_⟩
    rintro y ⟨n,rfl⟩
    exact (bound n).1
  obtain ⟨ν,invariant,k,P,limit⟩ := separated_gibbs_compact_limit T T.continuous φ univ ε
    εpositive s nonempty separated above below
  obtain ⟨H,entropyH⟩ := entropy_finite_of_expansive T c positive expansive ν invariant
  have comparison : (P.entropyRate T (ν : Measure X) : EReal) ≤ entropy T (ν : Measure X) := by
    unfold entropy
    apply le_iSup_of_le k
    apply le_iSup_of_le P
    rw [P.liminf_eq_entropyRate T (ν : Measure X) invariant]
  rw [entropyH] at comparison
  have realComparison := EReal.coe_le_coe_iff.mp comparison
  refine ⟨ν,invariant,?_⟩
  rw [entropyH,EReal.toReal_coe]
  exact limit.trans (add_le_add realComparison le_rfl)

end LeanShared.ThermodynamicDefinitions
