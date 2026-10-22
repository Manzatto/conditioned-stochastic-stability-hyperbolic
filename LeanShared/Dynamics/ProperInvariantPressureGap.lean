module

public import LeanShared.Dynamics.ExpansiveVariationalPrinciple
public import LeanShared.Dynamics.EquilibriumInvariantSubtype
public import LeanShared.Dynamics.InvariantCoreHomeomorphism

/-! A unique fully supported equilibrium forces a strict pressure gap
on every nonempty proper compact invariant subset.  An actual equilibrium
on that subset is produced by the proved expansive variational principle.
-/

public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem pressure_lt_of_unique_full_support (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (μ : ProbabilityMeasure X)
    (unique : ∀ η : ProbabilityMeasure X, IsEquilibriumState T φ univ η → η = μ)
    (fullSupport : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < (μ : Measure X) U)
    (K : Set X) (closedK : IsClosed K) (nonemptyK : K.Nonempty)
    (invariantK : T '' K = K) (properK : K ≠ univ) :
    pressure T φ K < pressure T φ univ := by
  let S := LeanShared.invariantCoreHomeomorphism T K invariantK
  let : CompactSpace K := isCompact_iff_compactSpace.mp closedK.isCompact
  let : Nonempty K := nonemptyK.to_subtype
  have forward (x : K) : (S x).val = T x.val := rfl
  have backward (x : K) : (S.symm x).val = T.symm x.val := rfl
  have expansiveK : ∀ x y : K, (∀ j : ℕ,
      dist ((S : K → K)^[j] x) ((S : K → K)^[j] y) ≤ c ∧
      dist ((S.symm : K → K)^[j] x) ((S.symm : K → K)^[j] y) ≤ c) → x = y := by
    intro x y close
    apply Subtype.ext
    apply expansive x.val y.val
    intro j
    have small := close j
    change dist (((S : K → K)^[j] x).val) (((S : K → K)^[j] y).val) ≤ c ∧
      dist (((S.symm : K → K)^[j] x).val) (((S.symm : K → K)^[j] y).val) ≤ c at small
    simpa only [iterate_coe_restriction S forward, iterate_coe_restriction S.symm backward] using small
  let φK : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => φ x.val, φ.continuous.comp continuous_subtype_val⟩
  obtain ⟨ν, equilibriumK⟩ := exists_expansive_equilibrium S c positiveC expansiveK φK
  have equilibrium := equilibriumK.map_subtype T K closedK.measurableSet T.continuous.measurable
    S forward φ φ.continuous.measurable ν
  have upper := entropy_free_energy_le_pressure T c positiveC expansive (ν.map Subtype.val)
    ⟨equilibrium.1, equilibrium.2.1⟩ φ
  rw [equilibrium.2.2.2.2] at upper
  apply lt_of_le_of_ne upper
  intro equal
  have equilibriumUniv : IsEquilibriumState T φ univ (ν.map Subtype.val) :=
    ⟨equilibrium.1, equilibrium.2.1, by simp, equilibrium.2.2.2.1,
      equilibrium.2.2.2.2.trans equal⟩
  have identical := unique (ν.map Subtype.val) equilibriumUniv
  have zeroMass := equilibrium.2.2.1
  rw [identical] at zeroMass
  have nonemptyComplement : Kᶜ.Nonempty := by
    by_contra empty
    apply properK
    apply eq_univ_of_forall
    intro x
    by_contra outside
    exact empty ⟨x, outside⟩
  have positiveMass := fullSupport Kᶜ closedK.isOpen_compl nonemptyComplement
  rw [zeroMass] at positiveMass
  exact (lt_irrefl _ positiveMass)

end LeanShared.ThermodynamicDefinitions
