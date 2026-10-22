module

public import LeanShared.Dynamics.ExpansiveProductPressure

/-! Independent products of actual equilibrium probabilities are actual
equilibrium probabilities for the additive product potential. No uniqueness
is inferred from component uniqueness. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

theorem IsEquilibriumState.product_of_expansive (T : X ≃ₜ X) (S : Y ≃ₜ Y) (c d : ℝ)
    (cpositive : 0 < c) (dpositive : 0 < d)
    (expansiveT : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (expansiveS : ∀ x y, (∀ n : ℕ,
      dist ((S : Y → Y)^[n] x) ((S : Y → Y)^[n] y) ≤ d ∧
      dist ((S.symm : Y → Y)^[n] x) ((S.symm : Y → Y)^[n] y) ≤ d) → x=y)
    (φ : X →ᵇ ℝ) (ψ : Y →ᵇ ℝ) (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (stateμ : IsEquilibriumState T φ univ μ) (stateν : IsEquilibriumState S ψ univ ν) :
    IsEquilibriumState (T.prodCongr S) (productPotential φ ψ) univ
      (⟨(μ : Measure X).prod (ν : Measure Y),inferInstance⟩ : ProbabilityMeasure (X × Y)) := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure (μ : Measure X)
  let : Nonempty Y := nonempty_of_isProbabilityMeasure (ν : Measure Y)
  have invμ : MeasurePreserving T (μ : Measure X) (μ : Measure X) := ⟨stateμ.1,stateμ.2.1⟩
  have invν : MeasurePreserving S (ν : Measure Y) (ν : Measure Y) := ⟨stateν.1,stateν.2.1⟩
  have inv := invμ.prod invν
  obtain ⟨HX,entropyX⟩ := entropy_finite_of_expansive T c cpositive expansiveT μ invμ
  obtain ⟨HY,entropyY⟩ := entropy_finite_of_expansive S d dpositive expansiveS ν invν
  have integrable := (productPotential φ ψ).integrable ((μ : Measure X).prod (ν : Measure Y))
  refine ⟨(T.prodCongr S).continuous.measurable,inv.map_eq,by simp,integrable,?_⟩
  change entropy (T.prodCongr S) ((μ : Measure X).prod (ν : Measure Y)) +
    ((∫ z, productPotential φ ψ z ∂((μ : Measure X).prod (ν : Measure Y)) : ℝ) : EReal) = _
  rw [entropy_product_eq T S c d cpositive dpositive expansiveT expansiveS μ ν invμ invν,
    integral_productPotential,
    (measurePreserving_fst (μ := (μ : Measure X)) (ν := (ν : Measure Y))).map_eq,
    (measurePreserving_snd (μ := (μ : Measure X)) (ν := (ν : Measure Y))).map_eq,
    pressure_product_eq T S c d cpositive dpositive expansiveT expansiveS φ ψ,
    ←stateμ.2.2.2.2,←stateν.2.2.2.2,entropyX,entropyY,
    ←EReal.coe_add,←EReal.coe_add,←EReal.coe_add,←EReal.coe_add]
  congr 1
  ring

end LeanShared.ThermodynamicDefinitions
