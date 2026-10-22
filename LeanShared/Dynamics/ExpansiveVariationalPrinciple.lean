module

public import LeanShared.Dynamics.ExpansivePressureUpperVariational
public import LeanShared.Dynamics.ExpansivePressureLowerVariational

/-! The actual Bowen separated pressure equals the attained full
Kolmogorov--Sinai entropy plus energy maximum on compact expansive systems.
An actual equilibrium probability is constructed, with no variational,
Gibbs, generating-partition, or equilibrium-existence input. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_expansive_equilibrium (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (φ : X →ᵇ ℝ) :
    ∃ μ : ProbabilityMeasure X, IsEquilibriumState T φ univ μ := by
  obtain ⟨μ,invariant,⟨H,entropyH⟩,maximal⟩ := exists_entropy_variational_maximizer T c positive expansive φ φ.continuous
  have upper := pressure_le_variational_maximum T c positive expansive φ
    ((entropy T (μ : Measure X)).toReal + ∫ x, φ x ∂(μ : Measure X)) maximal
  have lower := entropy_free_energy_le_pressure T c positive expansive μ invariant φ
  have normalization : entropy T (μ : Measure X) + ((∫ x, φ x ∂(μ : Measure X) : ℝ) : EReal) =
      (((entropy T (μ : Measure X)).toReal + ∫ x, φ x ∂(μ : Measure X) : ℝ) : EReal) := by
    rw [entropyH,EReal.toReal_coe,←EReal.coe_add]
  rw [←normalization] at upper
  refine ⟨μ,T.continuous.measurable,invariant.map_eq,?_,φ.integrable _,le_antisymm lower upper⟩
  simp

/-- The variational supremum ranges over every actual invariant Borel
probability and uses the literal full metric entropy. -/
theorem pressure_eq_variational_supremum (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (φ : X →ᵇ ℝ) :
    pressure T φ univ = ⨆ μ : ProbabilityMeasure X,
      ⨆ (_ : MeasurePreserving T (μ : Measure X) (μ : Measure X)),
        entropy T (μ : Measure X) + ((∫ x, φ x ∂(μ : Measure X) : ℝ) : EReal) := by
  obtain ⟨μ,equilibrium⟩ := exists_expansive_equilibrium T c positive expansive φ
  apply le_antisymm
  · rw [←equilibrium.2.2.2.2]
    exact le_iSup_of_le μ (le_iSup_of_le ⟨equilibrium.1,equilibrium.2.1⟩ le_rfl)
  · apply iSup_le
    intro ν
    apply iSup_le
    intro invariant
    exact entropy_free_energy_le_pressure T c positive expansive ν invariant φ

end LeanShared.ThermodynamicDefinitions
