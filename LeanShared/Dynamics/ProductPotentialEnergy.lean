module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual additive product potentials and their exact marginal energy identity. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[expose] def productPotential (φ : X →ᵇ ℝ) (ψ : Y →ᵇ ℝ) : X × Y →ᵇ ℝ :=
  φ.compContinuous ⟨Prod.fst,continuous_fst⟩ + ψ.compContinuous ⟨Prod.snd,continuous_snd⟩

@[simp] theorem productPotential_apply (φ : X →ᵇ ℝ) (ψ : Y →ᵇ ℝ) (z : X × Y) :
    productPotential φ ψ z=φ z.1+ψ z.2 := rfl

variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

theorem integral_productPotential (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (φ : X →ᵇ ℝ) (ψ : Y →ᵇ ℝ) :
    (∫ z, productPotential φ ψ z ∂μ) =
      (∫ x, φ x ∂μ.map Prod.fst)+(∫ y, ψ y ∂μ.map Prod.snd) := by
  have first := integral_map_of_stronglyMeasurable (μ := μ) measurable_fst φ.continuous.stronglyMeasurable
  have second := integral_map_of_stronglyMeasurable (μ := μ) measurable_snd ψ.continuous.stronglyMeasurable
  have intFirst : Integrable (fun z : X × Y => φ z.1) μ :=
    Integrable.comp_measurable (φ.integrable (μ.map Prod.fst)) measurable_fst
  have intSecond : Integrable (fun z : X × Y => ψ z.2) μ :=
    Integrable.comp_measurable (ψ.integrable (μ.map Prod.snd)) measurable_snd
  change (∫ z, φ z.1+ψ z.2 ∂μ) = _
  rw [integral_add intFirst intSecond,←first,←second]

end LeanShared.ThermodynamicDefinitions
