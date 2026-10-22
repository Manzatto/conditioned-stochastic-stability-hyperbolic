module
public import LeanShared.Dynamics.HyperbolicThermodynamics
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Exact compact-state marginals of a generated product local family.
The input family, its weak limit and equilibrium uniqueness are outputs of
the local source constructor. Only the deterministic product variational
identity is used to identify the original equilibrium limit. No second
probability family is chosen. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.CompactMarginalEquilibrium
open LeanShared
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- The original family is precisely the first marginal of the supplied
GENERATED product family, including its original equilibrium weak limit.
`Q` may be the literal closed layer of the product adapted filtration. -/
theorem from_generated_family
    (K : Set X) (Q : Set (X × Y)) (productSet : Q = K ×ˢ (univ : Set Y))
    (T : X ≃ₜ X) (S : Y ≃ₜ Y) (ψP : X × Y → ℝ) (ΛP : Set (X × Y))
    (νP : ℝ≥0 → ProbabilityMeasure Q) (ν₀P : ProbabilityMeasure Q)
    (νeqP : ProbabilityMeasure (X × Y))
    (limit : Tendsto νP (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀P))
    (mapped : (ν₀P : Measure Q).map Subtype.val = (νeqP : Measure (X × Y)))
    (unique : ∀ ζ : ProbabilityMeasure (X × Y),
      ThermodynamicDefinitions.IsEquilibriumState (T.prodCongr S) ψP ΛP ζ → ζ = νeqP)
    (νeq : ProbabilityMeasure X) (νaux : ProbabilityMeasure Y)
    (productEquilibrium : ThermodynamicDefinitions.IsEquilibriumState (T.prodCongr S) ψP ΛP
      (⟨(νeq : Measure X).prod (νaux : Measure Y), inferInstance⟩ : ProbabilityMeasure (X × Y))) :
    ∃ ν₀ : ProbabilityMeasure K, ∃ ν : ℝ≥0 → ProbabilityMeasure K,
      Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) ∧
      (ν₀ : Measure K).map Subtype.val = (νeq : Measure X) ∧
      ∀ ε, (ν ε : Measure K).map Subtype.val = (νP ε : Measure Q).map (fun z => z.val.1) := by
  let project : Q → K := fun z => ⟨z.val.1, by
    have hz : z.val ∈ K ×ˢ (univ : Set Y) := by simpa only [productSet] using z.property
    exact hz.1⟩
  have continuousProject : Continuous project :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have measurableProject := continuousProject.measurable
  let ν₀ := ν₀P.map project
  let ν := fun ε => (νP ε).map project
  have originalLimit : Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous νP ν₀P limit continuousProject
  have productIdentity : νeqP =
      (⟨(νeq : Measure X).prod (νaux : Measure Y), inferInstance⟩ : ProbabilityMeasure (X × Y)) :=
    (unique _ productEquilibrium).symm
  have originalMap : (ν₀ : Measure K).map Subtype.val = (νeq : Measure X) := by
    change ((ν₀P : Measure Q).map project).map Subtype.val = _
    rw [Measure.map_map measurable_subtype_coe measurableProject]
    have composition : (Subtype.val : K → X) ∘ project =
        Prod.fst ∘ (Subtype.val : Q → X × Y) := rfl
    rw [composition, ← Measure.map_map measurable_fst measurable_subtype_coe,
      mapped, productIdentity]
    change ((νeq : Measure X).prod (νaux : Measure Y)).map Prod.fst = (νeq : Measure X)
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  refine ⟨ν₀, ν, originalLimit, originalMap, ?_⟩
  intro ε
  change ((νP ε : Measure Q).map project).map Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe measurableProject]
  rfl

end ConditionedStochasticStabilityHyperbolic.Paper.CompactMarginalEquilibrium
