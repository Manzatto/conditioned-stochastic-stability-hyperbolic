module
public import LeanShared.Dynamics.PressureOrder
public import LeanShared.Dynamics.HyperbolicEnvelopePressure

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ClassicalPressureMetadata
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPositiveEnvelope
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPressureSlack
public import LeanShared.Geometry.LocalizationWordCylinders
public import LeanShared.Dynamics.HyperbolicThermodynamics

/-! Faithful ordinary deterministic pressure sources for the actual HL
manifold model. The fibers, differentials, cylinder family, survivor sets,
positive envelope, exponent pair and pressure scalar have literal meanings.
No strict coefficient, noisy Lasota--Yorke bound or spectral gap is a field.

The deterministic comparison is the cited BT subadditive/minimum-cover
pressure theorem including its hyperbolic survivor/shadowing/distortion
hypotheses. It concerns the actual intrinsic cocycle and full finite
survivors, not arbitrary densities bounded only on the invariant core.
Pressure order/Lipschitz continuity is a separate ordinary classical input.
This is explicitly the saddle BT branch: pure stable/unstable endpoints are
not silently asserted to follow from the cited anisotropic source. The
selected atlas has mesh below a genuine core expansivity scale.
-/

public noncomputable section
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff SchwartzMap BigOperators Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLPhysicalPressureSources
open LeanShared HyperbolicBasicSet
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
  {Params : Type*}

@[expose] def envelopeIncrement (hw : Continuous m.weight) (hwn : ∀ x, 0 ≤ m.weight x)
    (hagrees : EqOn m.weight g Λ) (δ : ℝ) (hδ : 0 < δ) : ℝ :=
  Classical.choose (h.exists_positive_envelope m.weight hw hwn hagrees hδ)

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [MetricSpace Ω]
  [MeasurableSpace M] [BorelSpace M] in
theorem envelopeIncrement_spec (hw : Continuous m.weight) (hwn : ∀ x, 0 ≤ m.weight x)
    (hagrees : EqOn m.weight g Λ) (δ : ℝ) (hδ : 0 < δ) :
    0 < envelopeIncrement m h hw hwn hagrees δ hδ ∧
      Continuous (fun x => m.weight x + envelopeIncrement m h hw hwn hagrees δ hδ) ∧
      (∀ x, 0 < m.weight x + envelopeIncrement m h hw hwn hagrees δ hδ) ∧
      ∀ x ∈ Λ, 0 ≤ Real.log (m.weight x + envelopeIncrement m h hw hwn hagrees δ hδ) - Real.log (g x) ∧
        Real.log (m.weight x + envelopeIncrement m h hw hwn hagrees δ hδ) - Real.log (g x) ≤ δ :=
  Classical.choose_spec (h.exists_positive_envelope m.weight hw hwn hagrees hδ)

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
  source : ∀ δ : ℝ, 0 < δ → PhysicalManifoldClassicalPressureSources.Data m
    (Fiber := fun x => TangentSpace (𝓘(ℝ, E)) x)
    (Params := Params) (I := fun N => Fin (N + 1) → m.localization.indices)
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

omit [BorelSpace M] [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] in
variable {m h} in
/-- Order of actual separated-set pressure is proved from finite Bowen sums. -/
theorem Data.pressure_order (_p : Data m h (Params := Params))
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
@[expose] def Data.envelopePressure (p : Data m h (Params := Params)) (δ : ℝ) (hδ : 0 < δ) : ℝ :=
  p.equilibrium.envelopePressure ((p.source δ hδ).envelope)

omit [BorelSpace M] [∀ k, CompleteSpace (LocalReg k)] [CompactSpace M] in
variable {m h} in
/-- The reference pressure and proved logarithmic envelope bound imply this
identity; no envelope-pressure source is supplied. -/
theorem Data.envelopePressure_identity (p : Data m h (Params := Params)) (δ : ℝ) (hδ : 0 < δ) :
    ThermodynamicDefinitions.pressure T
      (h.basic.hyperbolic.potential ((p.source δ hδ).envelope)) Λ =
        (p.envelopePressure δ hδ : EReal) := by
  apply (p.equilibrium.envelopePressure_spec ((p.source δ hδ).envelope) δ hδ.le _).1
  intro x hx
  rw [p.source_envelope δ hδ]
  exact (envelopeIncrement_spec m h p.weight_continuous p.weight_nonnegative
    p.weight_agrees δ hδ).2.2.2 x hx

namespace Data
variable (p : Data m h (Params := Params))

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
theorem envelope_pressure_upper (δ : ℝ) (hδ : 0 < δ) :
    p.envelopePressure δ hδ ≤ p.equilibrium.pressure + δ := by
  apply p.pressure_order
    (h.basic.hyperbolic.potential ((p.source δ hδ).envelope))
    (h.basic.hyperbolic.potential g) (p.envelopePressure δ hδ) p.equilibrium.pressure δ
    (p.envelopePressure_identity δ hδ) p.equilibrium.pressure_identity
  intro x hx
  have hlog := (envelopeIncrement_spec m h p.weight_continuous
    p.weight_nonnegative p.weight_agrees δ hδ).2.2.2 x hx
  rw [p.source_envelope δ hδ]
  unfold HyperbolicData.potential
  linarith [hlog.2]

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
theorem cover_pressure_upper (δ : ℝ) (hδ : 0 < δ) :
    (p.source δ hδ).Qpressure ≤ h.principalRate p.t p.s * Real.exp (p.equilibrium.pressure + δ) := by
  let C := max (h.basic.hyperbolic.constant ^ p.t) (h.basic.hyperbolic.constant ^ (-p.s))
  have hC : 0 < C := lt_max_of_lt_left (Real.rpow_pos_of_pos h.basic.hyperbolic.constant_pos p.t)
  have hbound := p.deterministic_cover δ hδ C (h.principalRate p.t p.s) hC
    (h.principalRate_pos p.t p.s)
    (fun N x hx => h.principal_max_bound p.t_positive.le p.s_negative.le N x hx)
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (p.envelope_pressure_upper m h δ hδ))
    (h.principalRate_pos p.t p.s).le)

/-- Output of the proved pressure selection; all strict inequalities are
constructed, not ordinary source fields. -/
structure Selected : Type _ where
  δ : ℝ
  δ_positive : 0 < δ
  ρ : ℝ
  ρ_positive : 0 < ρ
  strict : (p.source δ δ_positive).Qpressure < ρ
  below : ρ < Real.exp p.equilibrium.pressure

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
def selected : Selected m h p := by
  classical
  let Q := fun δ : ℝ => if hδ : 0 < δ then (p.source δ hδ).Qpressure else 0
  have comparison : ∀ δ, 0 < δ → Q δ ≤
      h.principalRate p.t p.s * Real.exp (p.equilibrium.pressure + δ) := by
    intro δ hδ
    simpa only [Q, dite_eq_left hδ] using p.cover_pressure_upper m h δ hδ
  have choice := h.exists_pressure_slack p.t_positive p.s_negative p.equilibrium.pressure Q comparison
  let δ := Classical.choose choice
  have dspec := Classical.choose_spec choice
  let ρ := Classical.choose dspec
  have rspec := Classical.choose_spec dspec
  have hδ : 0 < δ := rspec.1
  have hstrict : (p.source δ hδ).Qpressure < ρ := by
    have hQ : Q δ < ρ := rspec.2.2.1
    simpa only [Q, dite_eq_left hδ] using hQ
  exact ⟨δ, hδ, ρ, rspec.2.1, hstrict, rspec.2.2.2⟩

namespace Selected
variable (b : Selected m h p)

def sources : PhysicalManifoldPressureSources.Data m
    (Fiber := fun x => TangentSpace (𝓘(ℝ, E)) x)
    (Params := Params) (I := fun N => Fin (N + 1) → m.localization.indices) :=
  (p.source b.δ b.δ_positive).withRate m b.ρ b.strict

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
private theorem sources_rate_aux : (b.sources m h p).ρ = b.ρ :=
  (p.source b.δ b.δ_positive).withRate_rate m b.ρ b.strict

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
theorem sources_rate : (b.sources m h p).ρ = b.ρ := sources_rate_aux m h p b

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
theorem sources_positive : 0 < (b.sources m h p).ρ :=
  (b.sources_rate m h p).symm ▸ b.ρ_positive

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
theorem sources_below_pressure : (b.sources m h p).ρ < Real.exp p.equilibrium.pressure :=
  (b.sources_rate m h p).symm ▸ b.below

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
private theorem sources_reference_aux : (b.sources m h p).T = p.reference :=
  ((p.source b.δ b.δ_positive).withRate_reference m b.ρ b.strict).trans
    (p.source_reference b.δ b.δ_positive)

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
theorem sources_reference : (b.sources m h p).T = p.reference :=
  sources_reference_aux m h p b

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
private theorem sources_t_aux : (b.sources m h p).t = p.t :=
  ((p.source b.δ b.δ_positive).withRate_t m b.ρ b.strict).trans (p.source_t b.δ b.δ_positive)

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
private theorem sources_s_aux : (b.sources m h p).s = p.s :=
  ((p.source b.δ b.δ_positive).withRate_s m b.ρ b.strict).trans (p.source_s b.δ b.δ_positive)

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
theorem sources_exponents : ∀ i, m.exponent i true = (b.sources m h p).t ∧
    m.exponent i false = (b.sources m h p).s := by
  intro i
  exact ⟨(p.exponents i).1.trans (sources_t_aux m h p b).symm,
    (p.exponents i).2.trans (sources_s_aux m h p b).symm⟩

end Selected

end Data

end ConditionedStochasticStabilityHyperbolic.Paper.HLPhysicalPressureSources
