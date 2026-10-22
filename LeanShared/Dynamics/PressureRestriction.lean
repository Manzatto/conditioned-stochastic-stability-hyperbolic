module

public import LeanShared.Dynamics.ThermodynamicDefinitions

/-! Pressure and equilibrium states depend only on the potential on the
invariant core. This proves the manuscript's weight-agreement transfer
without assuming agreement on an entire collar. -/

@[expose] public noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators
namespace LeanShared.ThermodynamicDefinitions

variable {X : Type*} [MetricSpace X] {T : X → X} {K : Set X} {φ ψ : X → ℝ}

omit [MetricSpace X] in
theorem orbitSum_eq_of_eqOn (hT : MapsTo T K K) (h : EqOn φ ψ K)
    (n : ℕ) {x : X} (hx : x ∈ K) : orbitSum T φ n x = orbitSum T ψ n x := by
  apply Finset.sum_congr rfl
  intro i _hi
  exact h (hT.iterate i hx)

theorem separatedPartitionSum_eq_of_eqOn (hT : MapsTo T K K) (h : EqOn φ ψ K)
    (n : ℕ) (ε : ℝ) : separatedPartitionSum T φ K n ε = separatedPartitionSum T ψ K n ε := by
  classical
  unfold separatedPartitionSum
  congr 1
  funext s
  congr 1
  funext hs
  apply Finset.sum_congr rfl
  intro x hx
  rw [orbitSum_eq_of_eqOn hT h n (hs.1 x hx)]

theorem pressure_eq_of_eqOn (hT : MapsTo T K K) (h : EqOn φ ψ K) :
    pressure T φ K = pressure T ψ K := by
  unfold pressure
  congr 1
  funext ε
  congr 1
  funext n
  rw [separatedPartitionSum_eq_of_eqOn hT h]

variable [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- The same invariant core supports the same equilibrium probabilities
when the two potentials agree there. -/
theorem isEquilibriumState_iff_of_eqOn (hT : MapsTo T K K) (h : EqOn φ ψ K)
    (ν : ProbabilityMeasure X) :
    IsEquilibriumState T φ K ν ↔ IsEquilibriumState T ψ K ν := by
  have one {f g : X → ℝ} (heq : EqOn f g K)
      (hp : pressure T f K = pressure T g K) (hf : IsEquilibriumState T f K ν) :
      IsEquilibriumState T g K ν := by
    obtain ⟨hm, hi, hs, hint, he⟩ := hf
    have hae : f =ᵐ[(ν : Measure X)] g := by
      filter_upwards [show ∀ᵐ x ∂(ν : Measure X), x ∈ K from mem_ae_iff.mpr hs] with x hx
      exact heq hx
    refine ⟨hm, hi, hs, hint.congr hae, ?_⟩
    rw [← integral_congr_ae hae, ← hp]
    exact he
  exact ⟨one h (pressure_eq_of_eqOn hT h), one h.symm (pressure_eq_of_eqOn hT h.symm)⟩

end LeanShared.ThermodynamicDefinitions
