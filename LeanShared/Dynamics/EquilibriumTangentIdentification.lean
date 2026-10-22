module
public import LeanShared.Dynamics.CoreUniqueTangent
public import LeanShared.Dynamics.PressureRestriction
public import Mathlib.Topology.TietzeExtension

/-! The pressure tangent identifies the unique equilibrium. Only the values of a potential on the
compact invariant core matter: a potential continuous on the core is extended continuously
(Tietze), pressures and equilibrium states transfer along agreement on the core, and the
expansive tangent identification gives `ν = ∫ f dη`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Equilibrium states depend only on the potential on the invariant core. -/
theorem isEquilibriumState_congr {T : X → X} {K : Set X} (hT : MapsTo T K K) {φ ψ : X → ℝ}
    (h : EqOn φ ψ K) {ν : ProbabilityMeasure X}
    (hν : IsEquilibriumState T φ K ν) : IsEquilibriumState T ψ K ν := by
  obtain ⟨meas, inv, supp, integ, var⟩ := hν
  have ae : φ =ᵐ[(ν : Measure X)] ψ := by
    have : ∀ᵐ x ∂(ν : Measure X), x ∈ K := measure_eq_zero_iff_ae_notMem.mp supp |>.mono
      fun x hx => by simpa using hx
    exact this.mono fun x hx => h hx
  refine ⟨meas, inv, supp, integ.congr ae, ?_⟩
  rw [← integral_congr_ae ae, ← pressure_eq_of_eqOn hT h]
  exact var

/-- The pressure tangent of a potential continuous on an expansive core identifies its unique
equilibrium state. -/
theorem tangent_identification (T : X ≃ₜ X) (K : Set X) (compact : IsCompact K)
    (nonempty : K.Nonempty) (invariant : T '' K = K) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x ∈ K, ∀ y ∈ K, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (ψ f : X → ℝ) (continuousψ : ContinuousOn ψ K) (continuousF : Continuous f)
    (η : ProbabilityMeasure X) (hη : IsEquilibriumState T ψ K η)
    (unique : ∀ μ, IsEquilibriumState T ψ K μ → μ = η)
    (P : ℝ → ℝ) (hP : ∀ t, pressure T (fun x => ψ x + t * f x) K = P t) (ν : ℝ)
    (tangent : ∀ t : ℝ, t * ν ≤ P t - P 0) : ν = ∫ x, f x ∂(η : Measure X) := by
  have mapsTo : MapsTo (T : X → X) K K := fun x hx => invariant ▸ mem_image_of_mem _ hx
  have closedK := compact.isClosed
  let _ : Nonempty K := nonempty.to_subtype
  obtain ⟨φ, hφ⟩ := ContinuousMap.exists_extension closedK.isClosedEmbedding_subtypeVal
    ⟨fun x : K => ψ x, continuousψ.domRestrict⟩
  have agree : EqOn φ ψ K := fun x hx => by
    have := congrArg (fun F : C(K, ℝ) => F ⟨x, hx⟩) hφ
    exact this
  have hφP : ∀ t, pressure T (fun x => φ x + t * f x) K = P t := fun t => by
    rw [← hP t]
    exact pressure_eq_of_eqOn mapsTo fun x hx => by simp only [agree hx]
  have hηφ : IsEquilibriumState T φ K η :=
    isEquilibriumState_congr mapsTo (fun x hx => (agree hx).symm) hη
  have uniqueφ : ∀ μ, IsEquilibriumState T φ K μ → μ = η := fun μ hμ =>
    unique μ (isEquilibriumState_congr mapsTo agree hμ)
  exact core_tangent_eq T K compact nonempty invariant c positive expansive φ f φ.continuous
    continuousF η hηφ uniqueφ P hφP ν tangent

/-- The tangent family of a weight: if for every `t` the tilted weight `g e^{tψ}` has pressure
`P_t` with `t X ≤ P_t - P_0`, then `X = ∫ ψ dη`, where the potential of `g` is continuous on the
expansive core and `η` is its unique equilibrium. -/
theorem identification_of_tangent_family (T : X ≃ₜ X) (K : Set X) (compact : IsCompact K)
    (nonempty : K.Nonempty) (invariant : T '' K = K) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x ∈ K, ∀ y ∈ K, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (pot : (X → ℝ) → X → ℝ) (g ψ : X → ℝ) (continuousψ : Continuous ψ)
    (potCont : ContinuousOn (pot g) K)
    (tilted : ∀ t : ℝ, EqOn (pot (fun x => g x * Real.exp (t * ψ x))) (fun x => pot g x + t * ψ x) K)
    (P0 : ℝ) (hP0 : pressure T (pot g) K = (P0 : EReal))
    (η : ProbabilityMeasure X) (hη : IsEquilibriumState T (pot g) K η)
    (unique : ∀ μ, IsEquilibriumState T (pot g) K μ → μ = η) (Xval : ℝ)
    (family : ∀ t : ℝ, ∃ Pt : ℝ, pressure T (pot (fun x => g x * Real.exp (t * ψ x))) K =
      (Pt : EReal) ∧ t * Xval ≤ Pt - P0) :
    Xval = ∫ x, ψ x ∂(η : Measure X) := by
  choose Pfun hPfun hineq using family
  have mapsTo : MapsTo (T : X → X) K K := fun x hx => invariant ▸ mem_image_of_mem _ hx
  have hP : ∀ t, pressure T (fun x => pot g x + t * ψ x) K = (Pfun t : EReal) := fun t =>
    (pressure_eq_of_eqOn mapsTo (tilted t)).symm.trans (hPfun t)
  have zero : Pfun 0 = P0 := by
    have h0 := hP 0
    simp only [zero_mul, add_zero] at h0
    exact EReal.coe_injective (h0.symm.trans hP0)
  exact tangent_identification T K compact nonempty invariant c positive expansive (pot g) ψ
    potCont continuousψ η hη unique Pfun hP Xval (fun t => by rw [zero]; exact hineq t)

end LeanShared.ThermodynamicDefinitions
