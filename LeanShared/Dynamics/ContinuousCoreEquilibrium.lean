module

public import LeanShared.Dynamics.ExpansiveInvariantEquilibrium
public import LeanShared.Dynamics.PressureRestriction
public import Mathlib.Topology.TietzeExtension

/-! No ambient measurability or regularity of a potential is needed for
equilibrium existence on a compact invariant core: a genuine Tietze extension
and the proved core-restriction identities remove those extra hypotheses. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exists_equilibrium_of_continuousOn (T : X ≃ₜ X) (K : Set X)
    (compact : IsCompact K) (nonempty : K.Nonempty) (invariant : T '' K=K)
    (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x ∈ K, ∀ y ∈ K, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x=y)
    (φ : X → ℝ) (continuous : ContinuousOn φ K) :
    ∃ μ : ProbabilityMeasure X, IsEquilibriumState T φ K μ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp compact
  let f : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨(fun x => φ x.val),continuous.domRestrict⟩
  obtain ⟨g,_,extension⟩ := f.exists_extension_norm_eq_of_isClosedEmbedding
    compact.isClosed.isClosedEmbedding_subtypeVal
  have agreement : EqOn φ g K := by
    intro x hx
    exact (congrFun extension ⟨x,hx⟩).symm
  obtain ⟨μ,state⟩ := exists_equilibrium_on_compact_expansive T K compact nonempty invariant c positive
    expansive g g.continuous.measurable g.continuous.continuousOn
  refine ⟨μ,(isEquilibriumState_iff_of_eqOn ?_ agreement μ).mpr state⟩
  intro x hx
  rw [←invariant]
  exact ⟨x,hx,rfl⟩

end LeanShared.ThermodynamicDefinitions
