module
public import ConditionedStochasticStabilityHyperbolic.Paper.HLCorePressureComparison
public import LeanShared.Analysis.PressureIterateContraction

/-! Actual-HL application of BT (2008), Lemma 3.3. Its cited input is the
precise fixed-map iterate-pressure formula and ordinary pressure identities;
the desired gamma exp(P) bound is derived from the actual tangent factors.
Matching its scalar Q to a particular full-cylinder cover requires the
separate generating-cover/adapted-extension and endpoint comparison proofs. -/
@[expose] public noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Bundle Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)

def corePrincipalDensity (envelope : M → ℝ) (t s : ℝ) (N : ℕ) (x : M) : ℝ :=
  IntrinsicPrincipalDensity.density (fun _ : Unit => (T : M → M))
    (fun y => TangentSpace (𝓘(ℝ, E)) y) (fun _ => h.differential) envelope
    h.basic.hyperbolic.stable h.basic.hyperbolic.unstable N t s ((fun _ => ()), x)

def coreHyperbolicFactor (t s : ℝ) (N : ℕ) (x : M) : ℝ :=
  max
    (IntrinsicPrincipalDensity.stableFactor (fun _ : Unit => (T : M → M))
      (fun y => TangentSpace (𝓘(ℝ, E)) y) (fun _ => h.differential) (List.replicate N ()) x
      (h.basic.hyperbolic.stable (IntrinsicPrincipalDensity.orbit
        (fun _ : Unit => (T : M → M)) (List.replicate N ()) x)) ^ t)
    (IntrinsicPrincipalDensity.inverseFactor (fun _ : Unit => (T : M → M))
      (fun y => TangentSpace (𝓘(ℝ, E)) y) (fun _ => h.differential) (List.replicate N ()) x
      (h.basic.hyperbolic.unstable x) ^ (-s))

/-- Exact cited deterministic formulas, without a contraction/strict-gap
conclusion or a statement about arbitrary off-core extensions. -/
structure BTIterateFormula (envelope : M → ℝ) (t s P Q : ℝ) where
  PN : ℕ → ℝ
  finitePressure : ∀ N, 0 < N →
    ThermodynamicDefinitions.pressure ((T : M → M)^[N])
      (fun x => Real.log (h.corePrincipalDensity envelope t s N x)) Λ = (PN N : EReal)
  iteratePressure : ∀ N, 0 < N →
    ThermodynamicDefinitions.pressure ((T : M → M)^[N])
      (ThermodynamicDefinitions.orbitSum T (h.basic.hyperbolic.potential envelope) N) Λ =
        ((N : ℝ) * P : ℝ)
  order : ∀ N, 0 < N → ∀ (f k : M → ℝ) (Pf Pk c : ℝ),
    ThermodynamicDefinitions.pressure ((T : M → M)^[N]) f Λ = (Pf : EReal) →
    ThermodynamicDefinitions.pressure ((T : M → M)^[N]) k Λ = (Pk : EReal) →
    (∀ x ∈ Λ, f x ≤ k x + c) → Pf ≤ Pk + c
  limit : Tendsto (fun N : ℕ => Real.exp ((N : ℝ)⁻¹ * PN N)) atTop (𝓝 Q)

theorem deterministic_pressure_bound (envelope : M → ℝ) (t s P Q C γ : ℝ)
    (bt : h.BTIterateFormula envelope t s P Q)
    (positive : ∀ x ∈ Λ, 0 < envelope x)
    (dimension : ∀ x ∈ Λ, 0 < Module.finrank ℝ (h.basic.hyperbolic.unstable x))
    (hC : 0 < C) (hγ : 0 < γ)
    (bound : ∀ N x, x ∈ Λ → h.coreHyperbolicFactor t s N x ≤ C * γ ^ N) :
    Q ≤ γ * Real.exp P := by
  apply PressureIterateContraction.bound T Λ (h.basic.hyperbolic.potential envelope)
    (fun N x => Real.log (h.corePrincipalDensity envelope t s N x)) P Q C γ hC hγ
    bt.PN bt.finitePressure bt.iteratePressure bt.order _ bt.limit
  intro N hN x hx
  exact h.log_principal_density_le envelope positive dimension N t s C γ hC hγ (bound N) x hx

end ConditionedStochasticStabilityHyperbolic.Paper.HL
