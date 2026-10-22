module

public import LeanShared.Dynamics.ExpansiveVariationalPrinciple
public import LeanShared.Dynamics.ExpansiveEntropyProductAdd
public import LeanShared.Dynamics.ProductExpansivity
public import LeanShared.Dynamics.ProductPotentialEnergy

/-! Actual pressure addition for independent compact expansive systems,
proved from full variational principles and entropy bounds for every joining. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [Nonempty X] [Nonempty Y] [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
variable (T : X ≃ₜ X) (S : Y ≃ₜ Y) (c d : ℝ) (cpositive : 0 < c) (dpositive : 0 < d)
    (expansiveT : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (expansiveS : ∀ x y, (∀ n : ℕ,
      dist ((S : Y → Y)^[n] x) ((S : Y → Y)^[n] y) ≤ d ∧
      dist ((S.symm : Y → Y)^[n] x) ((S.symm : Y → Y)^[n] y) ≤ d) → x=y)
    (φ : X →ᵇ ℝ) (ψ : Y →ᵇ ℝ)

include c d cpositive dpositive expansiveT expansiveS in
theorem pressure_product_eq :
    pressure (T.prodCongr S) (productPotential φ ψ) univ = pressure T φ univ+pressure S ψ univ := by
  obtain ⟨PrX,pressureX⟩ := finite_pressure_of_expansive T c cpositive expansiveT φ φ.continuous
  obtain ⟨PrY,pressureY⟩ := finite_pressure_of_expansive S d dpositive expansiveS ψ ψ.continuous
  have expansive := product_expansivity T S c d expansiveT expansiveS
  have upper := pressure_le_variational_maximum (T.prodCongr S) (min c d) (lt_min cpositive dpositive)
    expansive (productPotential φ ψ) (PrX+PrY) (by
      intro ρ invariant
      let μX := ρ.map Prod.fst
      let μY := ρ.map Prod.snd
      have invX : MeasurePreserving T (μX : Measure X) (μX : Measure X) :=
        MeasurePreserving.of_semiconj ⟨measurable_fst,rfl⟩ invariant (fun _ => rfl) T.continuous.measurable
      have invY : MeasurePreserving S (μY : Measure Y) (μY : Measure Y) :=
        MeasurePreserving.of_semiconj ⟨measurable_snd,rfl⟩ invariant (fun _ => rfl) S.continuous.measurable
      obtain ⟨HX,entropyX⟩ := entropy_finite_of_expansive T c cpositive expansiveT μX invX
      obtain ⟨HY,entropyY⟩ := entropy_finite_of_expansive S d dpositive expansiveS μY invY
      obtain ⟨HP,entropyP⟩ := entropy_finite_of_expansive (T.prodCongr S) (min c d)
        (lt_min cpositive dpositive) expansive ρ invariant
      have entropyBound := entropy_joining_le T S c d cpositive dpositive expansiveT expansiveS ρ invariant
      rw [←(ProbabilityMeasure.toMeasure_map ρ (f := Prod.fst)),
        ←(ProbabilityMeasure.toMeasure_map ρ (f := Prod.snd)),entropyP,entropyX,entropyY,←EReal.coe_add] at entropyBound
      have entropyReal := EReal.coe_le_coe_iff.mp entropyBound
      have first := entropy_free_energy_le_pressure T c cpositive expansiveT μX invX φ
      have second := entropy_free_energy_le_pressure S d dpositive expansiveS μY invY ψ
      rw [entropyX,←EReal.coe_add,pressureX] at first
      rw [entropyY,←EReal.coe_add,pressureY] at second
      have firstReal := EReal.coe_le_coe_iff.mp first
      have secondReal := EReal.coe_le_coe_iff.mp second
      have energy := integral_productPotential (ρ : Measure (X × Y)) φ ψ
      change (∫ z, productPotential φ ψ z ∂(ρ : Measure (X × Y))) =
        (∫ x, φ x ∂(μX : Measure X))+(∫ y, ψ y ∂(μY : Measure Y)) at energy
      rw [entropyP,EReal.toReal_coe,energy]
      linarith)
  obtain ⟨μ,stateμ⟩ := exists_expansive_equilibrium T c cpositive expansiveT φ
  obtain ⟨ν,stateν⟩ := exists_expansive_equilibrium S d dpositive expansiveS ψ
  have invμ : MeasurePreserving T (μ : Measure X) (μ : Measure X) := ⟨stateμ.1,stateμ.2.1⟩
  have invν : MeasurePreserving S (ν : Measure Y) (ν : Measure Y) := ⟨stateν.1,stateν.2.1⟩
  let ρ : ProbabilityMeasure (X × Y) := ⟨(μ : Measure X).prod (ν : Measure Y),inferInstance⟩
  have invρ : MeasurePreserving (T.prodCongr S) (ρ : Measure (X × Y)) (ρ : Measure (X × Y)) := invμ.prod invν
  obtain ⟨HX,entropyX⟩ := entropy_finite_of_expansive T c cpositive expansiveT μ invμ
  obtain ⟨HY,entropyY⟩ := entropy_finite_of_expansive S d dpositive expansiveS ν invν
  have first := stateμ.2.2.2.2
  have second := stateν.2.2.2.2
  rw [entropyX,←EReal.coe_add,pressureX] at first
  rw [entropyY,←EReal.coe_add,pressureY] at second
  have firstReal := EReal.coe_injective first
  have secondReal := EReal.coe_injective second
  have energy := integral_productPotential ((μ : Measure X).prod (ν : Measure Y)) φ ψ
  rw [(measurePreserving_fst (μ := (μ : Measure X)) (ν := (ν : Measure Y))).map_eq,
    (measurePreserving_snd (μ := (μ : Measure X)) (ν := (ν : Measure Y))).map_eq] at energy
  have lower := entropy_free_energy_le_pressure (T.prodCongr S) (min c d)
    (lt_min cpositive dpositive) expansive ρ invρ (productPotential φ ψ)
  change entropy (T.prodCongr S) ((μ : Measure X).prod (ν : Measure Y)) +
    ((∫ z, productPotential φ ψ z ∂((μ : Measure X).prod (ν : Measure Y)) : ℝ) : EReal) ≤ _ at lower
  rw [entropy_product_eq T S c d cpositive dpositive expansiveT expansiveS μ ν invμ invν,
    entropyX,entropyY,energy,←EReal.coe_add,←EReal.coe_add] at lower
  have scalar : (HX+HY)+((∫ x, φ x ∂(μ : Measure X))+(∫ y, ψ y ∂(ν : Measure Y)))=PrX+PrY := by linarith
  rw [scalar] at lower
  rw [pressureX,pressureY,←EReal.coe_add]
  exact le_antisymm upper lower

end LeanShared.ThermodynamicDefinitions
