module

public import LeanShared.Dynamics.ExpansiveGibbsFreeEnergy

/-! A genuine uniform eventual separated Gibbs bound follows from the
invariant entropy-energy maximum; the finite sets and horizons are arbitrary. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]

theorem eventual_uniform_separated_free_energy
    (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (φ : X →ᵇ ℝ) (M : ℝ)
    (maximal : ∀ ν : ProbabilityMeasure X, MeasurePreserving T (ν : Measure X) (ν : Measure X) →
      (entropy T (ν : Measure X)).toReal + ∫ x, φ x ∂(ν : Measure X) ≤ M)
    (ε η : ℝ) (εpositive : 0 < ε) (ηpositive : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ s : Finset X, s.Nonempty → Separated T univ (n+1) ε s →
      Real.log (∑ x ∈ s, Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ) ≤ M+η := by
  classical
  let bad (n : ℕ) := ∃ s : Finset X, s.Nonempty ∧ Separated T univ (n+1) ε s ∧
    M+η < Real.log (∑ x ∈ s, Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ)
  let x : X := Classical.arbitrary X
  let s (n : ℕ) : Finset X := if h : bad n then h.choose else {x}
  have nonempty (n : ℕ) : (s n).Nonempty := by
    dsimp [s]
    split_ifs with h
    · exact h.choose_spec.1
    · exact Finset.singleton_nonempty x
  have separated (n : ℕ) : Separated T univ (n+1) ε (s n) := by
    dsimp [s]
    split_ifs with h
    · exact h.choose_spec.2.1
    · refine ⟨fun _ _ => mem_univ _,?_⟩
      intro y hy z hz different
      exact (different ((Finset.mem_singleton.mp hy).trans (Finset.mem_singleton.mp hz).symm)).elim
  obtain ⟨ν,invariant,bound⟩ := expansive_gibbs_free_energy T c positive expansive φ ε εpositive s nonempty separated
  have limsupBound := bound.trans (maximal ν invariant)
  obtain ⟨a,apos,counts⟩ := LeanShared.FiniteExpansiveWords.exists_uniform_card_bound T c positive expansive
  obtain ⟨p,count⟩ := counts ε εpositive
  have above : BddAbove (range (fun n => Real.log (∑ x ∈ s n,
      Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ))) := by
    refine ⟨(p+1 : ℝ)*Real.log (a : ℝ)+‖φ‖,?_⟩
    rintro y ⟨n,rfl⟩
    exact (normalized_gibbs_sum_bounds T φ n (s n) (nonempty n) a apos p
      ((count (n+1) (s n) (separated n)).trans
        (Nat.pow_le_pow_right (by omega) (by nlinarith : n+1+p ≤ (n+1)*(p+1))))).2
  by_contra failure
  have frequent : ∃ᶠ n in atTop, bad n := by
    rw [Filter.Frequently]
    intro noBad
    apply failure
    filter_upwards [noBad] with n hn
    intro q hq separatedq
    by_contra high
    exact hn ⟨q,hq,separatedq,lt_of_not_ge high⟩
  have lower : M+η ≤ limsup (fun n => Real.log (∑ x ∈ s n,
      Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ)) atTop := by
    apply le_limsup_of_frequently_le _ above.isBoundedUnder_of_range
    apply frequent.mono
    intro n hn
    have selected := hn.choose_spec.2.2
    simpa only [s,dite_eq_left hn] using selected.le
  linarith

end LeanShared.ThermodynamicDefinitions
