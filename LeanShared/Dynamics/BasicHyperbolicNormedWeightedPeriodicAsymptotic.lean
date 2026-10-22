module
public import LeanShared.Dynamics.HyperbolicLinearRechartPeriodic
public import LeanShared.Geometry.FractionalScalarLinearRechart
public import LeanShared.Dynamics.BasicHyperbolicWeightedPeriodicAsymptotic

/-! The actual weighted periodic asymptotic for the paper's general
finite-dimensional normed model. A Euclidean coordinate model and its
actual BasicData are constructed, with the supplied tangent metric
transported isometrically; all original physical coefficients agree. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Bundle IsManifold FractionalManifoldRegularity ThermodynamicDefinitions
open LinearRechartedManifold HyperbolicLinearRechart
open scoped Topology Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

theorem BasicData.actual_normed_weighted_periodic_asymptotic
    (b : BasicData (E := E) T Λ V)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm)
    (mixing : MixingOn T Λ) (g : M → ℝ)
    (weightRegular : Regular (E := E) (F := ℝ) q g)
    (weightPositive : ∀ x ∈ Λ, 0 < g x)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) :
    ∃ P : ℝ, pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧ ∃ τ D : ℝ,
      0 < τ ∧ τ < 1 ∧ 0 < D ∧ ∀ n : ℕ,
        |((Real.exp P) ^ (n + 1))⁻¹ *
          b.periodicPartitionSum forward inverse (b.hyperbolic.potential g) (n + 1) - 1| ≤
          D * τ ^ (n + 1) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let e : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq (by simp only [F,
    finrank_euclideanSpace, Fintype.card_fin])
  let oldPotential := b.hyperbolic.potential g
  let newBasic := transportBasic e b (forward.mdifferentiable (by simp))
    (inverse.mdifferentiable (by simp))
  have samePotential := basic_potential_eq e b (forward.mdifferentiable (by simp))
    (inverse.mdifferentiable (by simp)) g
  have sameSums (n : ℕ) := HyperbolicLinearRechart.periodicPartitionSum_eq
    e b forward inverse oldPotential n
  let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  let := charts (M := M) e
  let := manifold (M := M) e
  let : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
    ⟨transportMetric e original⟩
  let := continuous_metric (M := M) e
  let forwardNew := contMDiff_one_rechart e forward
  let inverseNew := contMDiff_one_rechart e inverse
  obtain ⟨P, pressureP, τ, D, positiveτ, smallτ, positiveD, bound⟩ :=
    newBasic.actual_weighted_periodic_asymptotic regularity weightOrder
      (forwardRegular.linearRechart e) (inverseRegular.linearRechart e)
      mixing g (weightRegular.scalarLinearRechart e) weightPositive forwardNew inverseNew
  have samePotential' : newBasic.hyperbolic.potential g = oldPotential := samePotential
  rw [samePotential'] at pressureP bound
  refine ⟨P, pressureP, τ, D, positiveτ, smallτ, positiveD, ?_⟩
  intro n
  have identity : newBasic.periodicPartitionSum forwardNew inverseNew oldPotential (n + 1) =
      b.periodicPartitionSum forward inverse oldPotential (n + 1) := sameSums (n + 1)
  simpa only [identity] using bound n

end LeanShared.HyperbolicBasicSet
