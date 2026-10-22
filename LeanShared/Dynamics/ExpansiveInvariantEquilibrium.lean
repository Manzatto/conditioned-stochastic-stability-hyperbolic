module

public import LeanShared.Dynamics.ExpansiveVariationalPrinciple
public import LeanShared.Dynamics.EquilibriumInvariantSubtype
public import Mathlib.Topology.Homeomorph.Lemmas

/-! Actual ambient equilibrium existence on a compact invariant expansive
subset, for a measurable potential continuous only on that subset. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exists_equilibrium_on_compact_expansive (T : X ≃ₜ X) (K : Set X)
    (compact : IsCompact K) (nonempty : K.Nonempty) (invariant : T '' K=K)
    (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x ∈ K, ∀ y ∈ K, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x=y)
    (φ : X → ℝ) (measurable : Measurable φ) (continuous : ContinuousOn φ K) :
    ∃ μ : ProbabilityMeasure X, IsEquilibriumState T φ K μ := by
  have iff_mem (x : X) : x ∈ K ↔ T x ∈ K := by
    constructor
    · intro hx
      rw [←invariant]
      exact ⟨x,hx,rfl⟩
    · intro hx
      rw [←invariant] at hx
      obtain ⟨y,hy,equal⟩ := hx
      exact (T.injective equal) ▸ hy
  let TK : K ≃ₜ K := T.subtype iff_mem
  let : CompactSpace K := isCompact_iff_compactSpace.mp compact
  let : Nonempty K := nonempty.to_subtype
  have forward (x : K) : (TK x).val=T x.val := rfl
  have backward (x : K) : (TK.symm x).val=T.symm x.val := rfl
  have restricted_expansive : ∀ x y : K, (∀ j : ℕ,
      dist ((TK : K → K)^[j] x) ((TK : K → K)^[j] y) ≤ c ∧
      dist ((TK.symm : K → K)^[j] x) ((TK.symm : K → K)^[j] y) ≤ c) → x=y := by
    intro x y small
    apply Subtype.ext
    apply expansive x.val x.property y.val y.property
    intro j
    have h := small j
    change dist (((TK : K → K)^[j] x).val) (((TK : K → K)^[j] y).val) ≤ c ∧
      dist (((TK.symm : K → K)^[j] x).val) (((TK.symm : K → K)^[j] y).val) ≤ c at h
    simpa only [iterate_coe_restriction TK forward,iterate_coe_restriction TK.symm backward] using h
  let f : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨(fun x => φ x.val),continuous.domRestrict⟩
  obtain ⟨μ,state⟩ := exists_expansive_equilibrium TK c positive restricted_expansive f
  refine ⟨μ.map Subtype.val,?_⟩
  exact IsEquilibriumState.map_subtype T K compact.isClosed.measurableSet T.continuous.measurable
    TK forward φ measurable μ state

end LeanShared.ThermodynamicDefinitions
