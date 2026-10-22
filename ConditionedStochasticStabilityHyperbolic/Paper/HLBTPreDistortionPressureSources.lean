module
public import LeanShared.Dynamics.PressureOrder
public import LeanShared.Dynamics.HyperbolicEnvelopePressure
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionPressureSources
public import ConditionedStochasticStabilityHyperbolic.Paper.HLBTIteratePressure
public import LeanShared.Analysis.ReferenceCylinderPressure
public import LeanShared.Dynamics.GeneratingOpenCylinders

/-! A faithful fixed-map BT source before the deterministic contraction deduction. It exposes
adapted all-survivor extensions and the precise positive-envelope/open-cover and
iterate-pressure formulas in Baladi--Tsujii (2008), §3 (3.2), Lemmas 3.2/3.3/3.5,
https://arxiv.org/abs/math/0606434 . The derived constructor below supplies the interface
after matching N+1 actual observations to N-letter BT covers, with only the fixed terminal
alphabet factor. -/

public noncomputable section
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff SchwartzMap BigOperators Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLBTPreDistortionPressureSources
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
  /-- Actual compact outer domain of the BT generating open cover. -/
  btRegion : Set M
  btRegion_compact : IsCompact btRegion
  btRegion_isolates : isolatedCore T btRegion = Λ
  bt_charts_contained : ∀ i : m.localization.indices, (m.atlas i).source ⊆ btRegion
  /-- Continuous genuine tangent splitting on the larger domain, including
  the terminal image required by an N-letter cylinder. -/
  bt_projection : ∀ δ : ℝ, 0 < δ → ∀ x : M,
    TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x
  bt_projection_range : ∀ δ hδ x, x ∈ btRegion ∪ T '' btRegion →
    (bt_projection δ hδ x).range = (source δ hδ).stable x
  bt_projection_kernel : ∀ δ hδ x, x ∈ btRegion ∪ T '' btRegion →
    (bt_projection δ hδ x).ker = (source δ hδ).unstable x
  bt_projection_idempotent : ∀ δ hδ x, x ∈ btRegion ∪ T '' btRegion →
    (bt_projection δ hδ x).comp (bt_projection δ hδ x) = bt_projection δ hδ x
  bt_projection_continuous : ∀ δ hδ, ContinuousOn
    (fun v : TangentBundle (𝓘(ℝ, E)) M =>
      (⟨v.proj, bt_projection δ hδ v.proj v.2⟩ : TangentBundle (𝓘(ℝ, E)) M))
    {v | v.proj ∈ btRegion ∪ T '' btRegion}
  /-- Ordinary adapted extension bounds, on ALL finite survivors, not only Λ.
  These are exactly the noninvariant preimage-stable and transported-unstable
  factors in BT (1.1), with the terminal image included in their domains. -/
  bt_adapted : ∀ δ hδ, ∃ C ell : ℝ, 0 < C ∧ 0 < ell ∧ ell < 1 ∧
    ∀ N : ℕ, 0 < N → ∀ x ∈ DeterministicWordCylinders.survivors
      (m.maps (source δ hδ).T) btRegion N,
      IntrinsicPrincipalDensity.stableFactor m.maps
        (fun y => TangentSpace (𝓘(ℝ, E)) y) (source δ hδ).differential
        (List.replicate N (source δ hδ).T) x
        ((source δ hδ).stable (IntrinsicPrincipalDensity.orbit m.maps
          (List.replicate N (source δ hδ).T) x)) ≤ C * ell ^ N ∧
      IntrinsicPrincipalDensity.inverseFactor m.maps
        (fun y => TangentSpace (𝓘(ℝ, E)) y) (source δ hδ).differential
        (List.replicate N (source δ hδ).T) x ((source δ hδ).unstable x) ≤ C * ell ^ N
  /-- Coarse full-cylinder boundedness, including the actual terminal tangent
  evaluation; this is not inferred from N+1-cylinder boundedness. -/
  bt_bounded : ∀ δ hδ N (labels : Fin N → m.localization.indices), BddAbove ({0} ∪
    (fun x => IntrinsicPrincipalDensity.density m.maps
      (fun y => TangentSpace (𝓘(ℝ, E)) y) (source δ hδ).differential
      (source δ hδ).envelope (source δ hδ).stable (source δ hδ).unstable
      N (source δ hδ).t (source δ hδ).s ((fun _ => (source δ hδ).T), x)) ''
    ((univ : Set M) ∩ DeterministicWordCylinders.cylinder (m.maps (source δ hδ).T)
      (fun i : m.localization.indices => (m.atlas i).source) N labels))
  btPressure : ∀ δ : ℝ, 0 < δ → ℝ
  /-- The primary-source fixed-map theorem: full open-cover asymptotic. -/
  bt_cover : ∀ δ hδ, Tendsto (fun N : ℕ =>
    ReferenceCylinderPressure.fullCost (m.maps (source δ hδ).T) (source δ hδ).K
      (fun i : m.localization.indices => (m.atlas i).source) N
      (fun x => IntrinsicPrincipalDensity.density m.maps
        (fun y => TangentSpace (𝓘(ℝ, E)) y) (source δ hδ).differential
        (source δ hδ).envelope (source δ hδ).stable (source δ hδ).unstable
        N (source δ hδ).t (source δ hδ).s ((fun _ => (source δ hδ).T), x)) ^ ((N : ℝ)⁻¹))
      atTop (𝓝 (btPressure δ hδ))
  /-- BT Lemma 3.3 plus the ordinary pressure order/iterate facts. This is
  an equality formula, containing no gamma or desired strict-gap bound. -/
  bt_iterate : ∀ δ hδ, h.BTIterateFormula (source δ hδ).envelope t s
    (equilibrium.envelopePressure ((source δ hδ).envelope)) (btPressure δ hδ)

omit [BorelSpace M] [∀ k, CompleteSpace (LocalReg k)]
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

def density (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (x : M) : ℝ :=
  IntrinsicPrincipalDensity.density m.maps (fun y => TangentSpace (𝓘(ℝ, E)) y)
    (p.source δ hδ).differential (p.source δ hδ).envelope
    (p.source δ hδ).stable (p.source δ hδ).unstable
    N (p.source δ hδ).t (p.source δ hδ).s ((fun _ => (p.source δ hδ).T), x)

def coefficient (δ : ℝ) (hδ : 0 < δ) (N : ℕ) : ℝ :=
  PressureCoverRefinement.coverCoefficient (p.source δ hδ).K
    (CylinderPrincipalCoefficient.fiber (p.source δ hδ).K ((p.source δ hδ).surviving N)
      (fun _ => (p.source δ hδ).T))
    (fun i => (fun x => ((fun _ : Fin N => (p.source δ hδ).T), x)) ⁻¹' (p.source δ hδ).chart N i)
    (p.density m h δ hδ N)

theorem coefficient_eq_reference (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    p.coefficient m h δ hδ N = ReferenceCylinderPressure.referenceCost m.maps
      (p.source δ hδ).T (p.source δ hδ).K
      (fun i : m.localization.indices => (m.atlas i).source) N (p.density m h δ hδ N) := by
  simp only [coefficient, ReferenceCylinderPressure.referenceCost,
    p.source_region δ hδ, p.source_chart δ hδ, p.source_surviving δ hδ,
    ConstructedManifoldLocalization.wordCylinder]

theorem coefficient_nonnegative (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    0 ≤ p.coefficient m h δ hδ N :=
  DomainPressureRefinement.coverCoefficient_nonneg_of_bdd
    ((p.source δ hδ).bounded N) ((p.source δ hδ).cover N)

theorem region_covered (δ : ℝ) (hδ : 0 < δ) :
    (p.source δ hδ).K ⊆ ⋃ i : m.localization.indices, (m.atlas i).source := by
  rw [p.source_region δ hδ]
  exact p.region_support.trans (ConstructedManifoldLocalization.selected_charts_cover m.atlas m.localization)

include p in
theorem alphabet_nonempty : Nonempty m.localization.indices := by
  obtain ⟨x, hx⟩ := h.nonempty_core
  obtain ⟨i, _⟩ := mem_iUnion.mp ((p.region_covered m h 1 (by norm_num))
    ((p.source 1 (by norm_num)).core_in_live (h.basic.subset_neighborhood hx)))
  exact ⟨i⟩

theorem source_pressure_le_BT (δ : ℝ) (hδ : 0 < δ) :
    (p.source δ hδ).Qpressure ≤ p.btPressure δ hδ := by
  have : Nonempty m.localization.indices := p.alphabet_nonempty m h
  apply PressureEndpointAsymptotic.comparison
    (fun N => p.coefficient m h δ hδ N)
    (fun N => ReferenceCylinderPressure.fullCost (m.maps (p.source δ hδ).T) (p.source δ hδ).K
      (fun i : m.localization.indices => (m.atlas i).source) N (p.density m h δ hδ N))
    (p.source δ hδ).Qpressure (p.btPressure δ hδ) (Fintype.card m.localization.indices)
    (Nat.cast_pos.mpr Fintype.card_pos) (p.coefficient_nonnegative m h δ hδ)
  · intro N
    exact DomainPressureRefinement.coverCoefficient_nonneg_of_bdd (p.bt_bounded δ hδ N)
      (DeterministicCylinderEndpoint.cover (m.maps (p.source δ hδ).T) (p.source δ hδ).K
        (fun i : m.localization.indices => (m.atlas i).source) (p.region_covered m h δ hδ) N)
  · exact Filter.Eventually.of_forall fun N => by
      rw [p.coefficient_eq_reference m h δ hδ N]
      exact ReferenceCylinderPressure.reference_le_full m.maps (p.source δ hδ).T
        (p.source δ hδ).K (fun i : m.localization.indices => (m.atlas i).source)
        (p.region_covered m h δ hδ) N (p.density m h δ hδ N) (p.bt_bounded δ hδ N)
  · exact (p.source δ hδ).pressure
  · exact p.bt_cover δ hδ

include p in
/-- The actual selected open atlas is genuinely generating on the adapted
outer domain; no survivor restriction is built into the cylinders. -/
theorem generating (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      ∀ forward backward : Fin n → m.localization.indices,
      ∀ x ∈ GeneratingOpenCylinders.cylinder T
        (fun i : m.localization.indices => (m.atlas i).source) forward backward,
      ∀ y ∈ GeneratingOpenCylinders.cylinder T
        (fun i : m.localization.indices => (m.atlas i).source) forward backward, dist x y < ε := by
  apply GeneratingOpenCylinders.generating T p.btRegion_compact p.pressureScale
    (fun i : m.localization.indices => (m.atlas i).source) p.bt_charts_contained _ _ ε hε
  · intro i x hx y hy
    exact (p.atlas_mesh i x hx y hy).le.trans (by linarith [p.pressureScale_positive])
  · intro x hx y hy hxy
    apply p.expansive x (p.btRegion_isolates ▸ hx) y (p.btRegion_isolates ▸ hy)
    intro n
    by_cases hn : 0 ≤ n
    · simpa only [HyperbolicBasicSet.orbit, ite_eq_left hn] using (hxy n.toNat).1
    · simpa only [HyperbolicBasicSet.orbit, ite_eq_right hn] using (hxy (-n).toNat).2

/-- Supplies the assumed deterministic_cover conclusion. -/
def constructed : HLPreDistortionPressureSources.Data m h where
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
  source := p.source
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
  deterministic_cover := by
    intro δ hδ C γ hC hγ bound
    apply (p.source_pressure_le_BT m h δ hδ).trans
    apply h.deterministic_pressure_bound (p.source δ hδ).envelope p.t p.s
      (p.envelopePressure δ hδ) (p.btPressure δ hδ) C γ (p.bt_iterate δ hδ)
    · intro x hx
      rw [p.source_envelope δ hδ]
      exact (envelopeIncrement_spec m h p.weight_continuous p.weight_nonnegative p.weight_agrees δ hδ).2.2.1 x
    · exact p.unstable_dimension
    · exact hC
    · exact hγ
    · exact bound

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.HLBTPreDistortionPressureSources
