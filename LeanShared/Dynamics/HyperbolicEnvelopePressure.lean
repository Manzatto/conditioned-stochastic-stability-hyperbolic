module

public import LeanShared.Dynamics.HyperbolicThermodynamics
public import LeanShared.Dynamics.PressureEnvelope

/-! The finite reference equilibrium pressure constructs the real pressure of
every bounded logarithmic envelope. No envelope-pressure oracle is required. -/
public noncomputable section
open Set MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle
namespace LeanShared.HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace M] [BorelSpace M]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ} {g : M → ℝ}

/-- The pressure scalar is the actual extended pressure's real part. -/
def EquilibriumPackage.envelopePressure (_e : EquilibriumPackage h g) (w : M → ℝ) : ℝ :=
  (ThermodynamicDefinitions.pressure T (h.potential w) Λ).toReal

omit [BorelSpace M] in
/-- Positivity-envelope estimates already proved by cutoff calculus imply
both the actual pressure identity and its sharp bounds. -/
theorem EquilibriumPackage.envelopePressure_spec (e : EquilibriumPackage h g)
    (w : M → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (logarithms : ∀ x ∈ Λ, 0 ≤ Real.log (w x)-Real.log (g x) ∧
      Real.log (w x)-Real.log (g x) ≤ δ) :
    ThermodynamicDefinitions.pressure T (h.potential w) Λ=(e.envelopePressure w : EReal) ∧
      e.pressure ≤ e.envelopePressure w ∧ e.envelopePressure w ≤ e.pressure+δ := by
  have invariant : MapsTo (T : M → M) Λ Λ := by
    intro x hx
    rw [←h.invariant]
    exact ⟨x,hx,rfl⟩
  obtain ⟨Q,identity,lower,upper⟩ := ThermodynamicDefinitions.finite_log_envelope_pressure
    invariant g w (fun x => Real.log (h.unstableJacobian x)) e.pressure δ
    e.pressure_identity hδ logarithms
  have scalar : e.envelopePressure w=Q := by
    unfold envelopePressure
    change (ThermodynamicDefinitions.pressure T
      (fun x => Real.log (w x)-Real.log (h.unstableJacobian x)) Λ).toReal=Q
    rw [identity]
    rfl
  rw [scalar]
  exact ⟨identity,lower,upper⟩

end LeanShared.HyperbolicBasicSet
