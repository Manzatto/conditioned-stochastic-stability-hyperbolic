module

public import LeanShared.Dynamics.BasicHyperbolicMainRuelleAsymptotic
public import LeanShared.Dynamics.BasicHyperbolicWeightedExponentialPotential
public import LeanShared.Dynamics.BasicHyperbolicPeriodicCoboundary

/-! The literal log-weight minus unstable-Jacobian periodic sums of the
original mixing BasicData have leading exp(nP) and a strict geometric
relative error.  The regular representative, full coding, variation,
primitive main graph, positive Ruelle eigenvalue and correction pressure
gap are all produced.  The original continuous tangent metric is retained.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Bundle IsManifold FractionalManifoldRegularity ThermodynamicDefinitions
open BilateralShadowingCoding MarkovFinitePathRealization
open scoped Topology Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

theorem BasicData.actual_weighted_periodic_asymptotic (b : BasicData (E := E) T Λ V)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm)
    (mixing : MixingOn T Λ) (g : M → ℝ) (weightRegular : Regular (E := E) (F := ℝ) q g)
    (weightPositive : ∀ x ∈ Λ, 0 < g x)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) :
    ∃ P : ℝ, pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧ ∃ τ D : ℝ,
      0 < τ ∧ τ < 1 ∧ 0 < D ∧ ∀ n : ℕ,
        |((Real.exp P) ^ (n + 1))⁻¹ *
          b.periodicPartitionSum forward inverse (b.hyperbolic.potential g) (n + 1) - 1| ≤ D * τ ^ (n + 1) := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨α, positiveα, smallα, ψ, regularψ, u, _continuousU, same, pressureSame, _periodicSame,
      _N, rectangles, code, properties, variation⟩ :=
    b.exists_weighted_exponential_potential regularity weightOrder forwardRegular inverseRegular
      g weightRegular weightPositive
  obtain ⟨P, pressureP, τ, D, positiveτ, smallτ, positiveD, bound⟩ :=
    b.periodic_asymptotic_of_actual_coding forward inverse mixing ψ α positiveα smallα regularψ
      rectangles code properties variation
  refine ⟨P, pressureSame.trans pressureP, τ, D, positiveτ, smallτ, positiveD, ?_⟩
  intro n
  rw [b.periodic_partition_coboundary forward inverse (b.hyperbolic.potential g) ψ u same (n + 1)]
  exact bound n

end LeanShared.HyperbolicBasicSet
