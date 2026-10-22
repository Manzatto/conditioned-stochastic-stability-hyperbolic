module

public import LeanShared.Dynamics.HyperbolicThermodynamics
public import LeanShared.Dynamics.PressureRestriction

/-! Replacing a cutoff away from the basic set preserves the genuine
thermodynamic state and pressure. No agreement on a collar is needed for
this deterministic identification (process correspondence uses more). -/

@[expose] public noncomputable section
open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.HyperbolicBasicSet
open ThermodynamicDefinitions
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace M] [BorelSpace M]
  {T : M ≃ₜ M} {Λ : Set M} {b : HyperbolicData (E := E) T Λ}
  {g : M → ℝ} (e : EquilibriumPackage b g)

def EquilibriumPackage.reweight (w : M → ℝ) (agree : EqOn w g Λ) :
    EquilibriumPackage b w := by
  have invariant : MapsTo T Λ Λ := fun x hx => b.invariant ▸ mem_image_of_mem T hx
  have potential : EqOn (b.potential w) (b.potential g) Λ := by
    intro x hx
    change Real.log (w x) - Real.log (b.unstableJacobian x) =
      Real.log (g x) - Real.log (b.unstableJacobian x)
    rw [agree hx]
  exact {
    pressure := e.pressure
    pressure_identity := (pressure_eq_of_eqOn invariant potential).trans e.pressure_identity
    state := e.state
    equilibrium := (isEquilibriumState_iff_of_eqOn invariant potential e.state).mpr e.equilibrium
    unique := fun ν hν => e.unique ν
      ((isEquilibriumState_iff_of_eqOn invariant potential ν).mp hν) }

omit [BorelSpace M] in
theorem EquilibriumPackage.reweight_state (w : M → ℝ) (agree : EqOn w g Λ) :
    (e.reweight w agree).state = e.state := rfl

omit [BorelSpace M] in
theorem EquilibriumPackage.reweight_pressure (w : M → ℝ) (agree : EqOn w g Λ) :
    (e.reweight w agree).pressure = e.pressure := rfl

end LeanShared.HyperbolicBasicSet
