module
public import LeanShared.Dynamics.PressureOrder
public import LeanShared.Dynamics.HyperbolicEnvelopePressure

public import ConditionedStochasticStabilityHyperbolic.Paper.HLPhysicalPressureSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldPreDistortionSources
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPreControlPressureSources
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldPreDistortionSources

/-! Faithful HL source BEFORE random robustness and separate-to-joint distortion. Only deterministic/ordinary
local calculus and microscopic kernel facts are inputs. Actual common chart
word controls, valid neighborhoods, strict pressure slack, finite-block
Lasota--Yorke estimates and annealed operators are constructed downstream. -/

public noncomputable section
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff SchwartzMap BigOperators Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionPressureSources
open LeanShared HyperbolicBasicSet
open HLPhysicalPressureSources
variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*}
  [∀ k, NormedAddCommGroup (LocalReg k)] [∀ k, NormedSpace ℂ (LocalReg k)]
  [∀ k, CompleteSpace (LocalReg k)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
variable [MetricSpace Ω]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ : Set M}
  (h : Paper.HL (E := E) T g Λ V)



structure Data where
  maps : Ω → M ≃ₜ M
  maps_eq : ∀ a, m.maps a = maps a
  maps_differentiable : ∀ a, MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (maps a)
  inverse_differentiable : ∀ a, MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (maps a).symm
  reference : Ω
  reference_eq : maps reference = T
  region : Set M
  region_isolates : isolatedCore T region = Λ
  region_support : region ⊆ S
  pressureScale : ℝ
  pressureScale_positive : 0 < pressureScale
  expansive : ∀ x ∈ Λ, ∀ y ∈ Λ,
    (∀ n : ℤ, dist (HyperbolicBasicSet.orbit T x n) (HyperbolicBasicSet.orbit T y n) ≤ pressureScale) → x = y
  atlas_mesh : ∀ i : m.localization.indices, ∀ x ∈ (m.atlas i).source,
    ∀ y ∈ (m.atlas i).source, dist x y < pressureScale / 4
  t : ℝ
  s : ℝ
  t_positive : 0 < t
  s_negative : s < 0
  admissible : t - s < h.r - 1
  stable_dimension : ∀ x ∈ Λ, 0 < Module.finrank ℝ (h.basic.hyperbolic.stable x)
  unstable_dimension : ∀ x ∈ Λ, 0 < Module.finrank ℝ (h.basic.hyperbolic.unstable x)
  exponents : ∀ i, m.exponent i true = t ∧ m.exponent i false = s
  processWeight : M → ℝ
  cutoff : M → ℝ
  cutoff_smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ cutoff
  cutoff_bounds : ∀ x, 0 ≤ cutoff x ∧ cutoff x ≤ 1
  cutoff_identity : m.weight = cutoff * processWeight
  retained : Set M
  retained_core : Λ ⊆ retained
  retained_agreement : EqOn m.weight processWeight (closure retained)
  cutoff_support : tsupport m.weight ⊆ interior region
  weight_continuous : Continuous m.weight
  weight_nonnegative : ∀ x, 0 ≤ m.weight x
  weight_agrees : EqOn m.weight g Λ
  equilibrium : EquilibriumPackage h.basic.hyperbolic g
  source : ∀ δ : ℝ, 0 < δ → PhysicalManifoldPreDistortionSources.Data m
    (Fiber := fun x => TangentSpace (𝓘(ℝ, E)) x)
    (I := fun N => Fin (N + 1) → m.localization.indices)
  source_regularity : ∀ δ hδ, (source δ hδ).r = h.r
  source_reference : ∀ δ hδ, (source δ hδ).T = reference
  source_region : ∀ δ hδ, (source δ hδ).K = region
  source_t : ∀ δ hδ, (source δ hδ).t = t
  source_s : ∀ δ hδ, (source δ hδ).s = s
  source_differential : ∀ δ hδ a x, (source δ hδ).differential a x =
    DiffeomorphismDifferential.differential (maps a)
      (maps_differentiable a) (inverse_differentiable a) x
  source_stable : ∀ δ hδ x, x ∈ Λ → (source δ hδ).stable x = h.basic.hyperbolic.stable x
  source_unstable : ∀ δ hδ x, x ∈ Λ → (source δ hδ).unstable x = h.basic.hyperbolic.unstable x
  source_envelope : ∀ δ hδ, (source δ hδ).envelope =
    fun x => m.weight x + envelopeIncrement m h weight_continuous weight_nonnegative weight_agrees δ hδ
  source_chart : ∀ δ hδ, (source δ hδ).chart =
    fun N => ConstructedManifoldLocalization.wordCylinder m.atlas m.localization m.maps N
  source_surviving : ∀ δ hδ, (source δ hδ).surviving =
    FiniteWordCylinders.survivors m.maps region
  deterministic_cover : ∀ δ hδ (C γ : ℝ), 0 < C → 0 < γ →
    (∀ N x, x ∈ Λ →
      max
        ((IntrinsicPrincipalDensity.stableFactor (fun _ : Unit => (T : M → M))
          (fun x => TangentSpace (𝓘(ℝ, E)) x) (fun _ => h.differential)
          (List.replicate N ()) x (h.basic.hyperbolic.stable
            (IntrinsicPrincipalDensity.orbit (fun _ : Unit => (T : M → M)) (List.replicate N ()) x))) ^ t)
        ((IntrinsicPrincipalDensity.inverseFactor (fun _ : Unit => (T : M → M))
          (fun x => TangentSpace (𝓘(ℝ, E)) x) (fun _ => h.differential)
          (List.replicate N ()) x (h.basic.hyperbolic.unstable x)) ^ (-s)) ≤ C * γ ^ N) →
    (source δ hδ).Qpressure ≤ γ * Real.exp (equilibrium.envelopePressure ((source δ hδ).envelope))

omit [BorelSpace M] [∀ k, CompleteSpace (LocalReg k)] in
variable {m h} in
/-- Order of actual separated-set pressure is proved from finite Bowen sums. -/
theorem Data.pressure_order (_p : Data m h)
    (φ ψ : M → ℝ) (Pφ Pψ c : ℝ)
    (first : ThermodynamicDefinitions.pressure T φ Λ = (Pφ : EReal))
    (second : ThermodynamicDefinitions.pressure T ψ Λ = (Pψ : EReal))
    (bound : ∀ x ∈ Λ, φ x ≤ ψ x+c) : Pφ ≤ Pψ+c := by
  apply ThermodynamicDefinitions.pressure_order (T := (T : M → M)) _ c Pφ Pψ first second bound
  intro x hx
  rw [←h.basic.hyperbolic.invariant]
  exact ⟨x,hx,rfl⟩

variable {m h} in
/-- The envelope pressure scalar is computed from the actual potential. -/
@[expose] def Data.envelopePressure (p : Data m h) (δ : ℝ) (hδ : 0 < δ) : ℝ :=
  p.equilibrium.envelopePressure ((p.source δ hδ).envelope)

omit [BorelSpace M] [∀ k, CompleteSpace (LocalReg k)] in
variable {m h} in
/-- The reference pressure and proved logarithmic envelope bound imply this
identity; no envelope-pressure source is supplied. -/
theorem Data.envelopePressure_identity (p : Data m h) (δ : ℝ) (hδ : 0 < δ) :
    ThermodynamicDefinitions.pressure T
      (h.basic.hyperbolic.potential ((p.source δ hδ).envelope)) Λ =
        (p.envelopePressure δ hδ : EReal) := by
  apply (p.equilibrium.envelopePressure_spec ((p.source δ hδ).envelope) δ hδ.le _).1
  intro x hx
  rw [p.source_envelope δ hδ]
  exact (envelopeIncrement_spec m h p.weight_continuous p.weight_nonnegative
    p.weight_agrees δ hδ).2.2.2 x hx

namespace Data
variable (p : Data m h)

set_option maxHeartbeats 1600000 in
def constructed : HLPreControlPressureSources.Data m h where
  maps := p.maps
  maps_eq := p.maps_eq
  maps_differentiable := p.maps_differentiable
  inverse_differentiable := p.inverse_differentiable
  reference := p.reference
  reference_eq := p.reference_eq
  region := p.region
  region_isolates := p.region_isolates
  region_support := p.region_support
  pressureScale := p.pressureScale
  pressureScale_positive := p.pressureScale_positive
  expansive := p.expansive
  atlas_mesh := p.atlas_mesh
  t := p.t
  s := p.s
  t_positive := p.t_positive
  s_negative := p.s_negative
  admissible := p.admissible
  stable_dimension := p.stable_dimension
  unstable_dimension := p.unstable_dimension
  exponents := p.exponents
  processWeight := p.processWeight
  cutoff := p.cutoff
  cutoff_smooth := p.cutoff_smooth
  cutoff_bounds := p.cutoff_bounds
  cutoff_identity := p.cutoff_identity
  retained := p.retained
  retained_core := p.retained_core
  retained_agreement := p.retained_agreement
  cutoff_support := p.cutoff_support
  weight_continuous := p.weight_continuous
  weight_nonnegative := p.weight_nonnegative
  weight_agrees := p.weight_agrees
  equilibrium := p.equilibrium
  source := fun δ hδ => (p.source δ hδ).constructed m
  source_regularity := p.source_regularity
  source_reference := p.source_reference
  source_region := p.source_region
  source_t := p.source_t
  source_s := p.source_s
  source_differential := p.source_differential
  source_stable := p.source_stable
  source_unstable := p.source_unstable
  source_envelope := p.source_envelope
  source_chart := p.source_chart
  source_surviving := p.source_surviving
  deterministic_cover := p.deterministic_cover

omit [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
private theorem constructed_reference_aux : (p.constructed m h).reference = p.reference := rfl

omit [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
theorem constructed_reference : (p.constructed m h).reference = p.reference :=
  constructed_reference_aux m h p

omit [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
private theorem constructed_equilibrium_aux : (p.constructed m h).equilibrium = p.equilibrium := rfl

omit [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
theorem constructed_equilibrium : (p.constructed m h).equilibrium = p.equilibrium :=
  constructed_equilibrium_aux m h p

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionPressureSources
