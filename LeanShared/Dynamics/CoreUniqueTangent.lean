module
public import LeanShared.Dynamics.ExpansiveUniqueTangent
public import LeanShared.Dynamics.EquilibriumCoreRestriction
public import LeanShared.Dynamics.EquilibriumInvariantSubtype
public import LeanShared.Dynamics.PressureInvariantSubtype

/-! The pressure-tangent identification on a compact invariant expansive core: the ambient potential
`φ` restricted to `K` has a unique equilibrium `η`; if `t ν ≤ P(φ + t f) - P(φ)` on `K` for
every real `t`, then `ν = ∫ f dη`. The statement is transported to the invariant subtype, where
the abstract tangent lemma applies. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set Function MeasureTheory Filter
open scoped BoundedContinuousFunction Topology
namespace LeanShared.ThermodynamicDefinitions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem core_tangent_eq (T : X ≃ₜ X) (K : Set X) (compact : IsCompact K) (nonempty : K.Nonempty)
    (invariant : T '' K = K) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x ∈ K, ∀ y ∈ K, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ f : X → ℝ) (continuousφ : Continuous φ) (continuousF : Continuous f)
    (η : ProbabilityMeasure X) (hη : IsEquilibriumState T φ K η)
    (unique : ∀ μ, IsEquilibriumState T φ K μ → μ = η)
    (P : ℝ → ℝ) (hP : ∀ t, pressure T (fun x => φ x + t * f x) K = P t) (ν : ℝ)
    (tangent : ∀ t : ℝ, t * ν ≤ P t - P 0) : ν = ∫ x, f x ∂(η : Measure X) := by
  have iff_mem (x : X) : x ∈ K ↔ T x ∈ K := by
    constructor
    · intro hx
      rw [← invariant]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← invariant] at hx
      obtain ⟨y, hy, equal⟩ := hx
      exact (T.injective equal) ▸ hy
  let S : K ≃ₜ K := T.subtype iff_mem
  let : CompactSpace K := isCompact_iff_compactSpace.mp compact
  let : Nonempty K := nonempty.to_subtype
  have forward (x : K) : (S x).val = T x.val := rfl
  have backward (x : K) : (S.symm x).val = T.symm x.val := rfl
  have measurableK : MeasurableSet K := compact.isClosed.measurableSet
  have expansiveS : ∀ x y : K, (∀ j : ℕ,
      dist ((S : K → K)^[j] x) ((S : K → K)^[j] y) ≤ c ∧
      dist ((S.symm : K → K)^[j] x) ((S.symm : K → K)^[j] y) ≤ c) → x = y := by
    intro x y close
    apply Subtype.ext
    apply expansive x.val x.property y.val y.property
    intro j
    have small := close j
    change dist (((S : K → K)^[j] x).val) (((S : K → K)^[j] y).val) ≤ c ∧
      dist (((S.symm : K → K)^[j] x).val) (((S.symm : K → K)^[j] y).val) ≤ c at small
    simpa only [iterate_coe_restriction S forward, iterate_coe_restriction S.symm backward] using small
  let φK : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => φ x.val, continuousφ.comp continuous_subtype_val⟩
  let fK : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => f x.val, continuousF.comp continuous_subtype_val⟩
  obtain ⟨ηK, push, stateK⟩ := hη.exists_core_restriction T K measurableK S S.continuous.measurable
    forward φ η
  have stateK' : IsEquilibriumState S φK univ ηK := stateK
  have uniqueK : ∀ μ, IsEquilibriumState S φK univ μ → μ = ηK := by
    intro μ hμ
    have ambient := IsEquilibriumState.map_subtype T K measurableK T.continuous.measurable S forward
      φ continuousφ.measurable μ hμ
    have same := unique _ ambient
    apply ProbabilityMeasure.toMeasure_injective
    have embedding := MeasurableEmbedding.subtype_coe measurableK
    have h1 : ((μ : Measure K)).map Subtype.val = (ηK : Measure K).map Subtype.val := by
      rw [push]
      exact congrArg (fun ρ : ProbabilityMeasure X => (ρ : Measure X)) same
    rw [← embedding.comap_map (μ : Measure K), ← embedding.comap_map (ηK : Measure K), h1]
  have pressureK (t : ℝ) : pressure S (φK + t • fK) univ = P t := by
    rw [← hP t, ← pressure_restriction S forward]
    rfl
  have result := tangent_eq S c positive expansiveS φK fK ηK stateK' uniqueK P pressureK ν tangent
  rw [result]
  change ∫ x, f x.val ∂(ηK : Measure K) = _
  rw [← integral_map (continuous_subtype_val.measurable.aemeasurable)
    continuousF.aestronglyMeasurable, push]

end LeanShared.ThermodynamicDefinitions
