module

public import LeanShared.Dynamics.BasicHyperbolicWeightedSymbolicPotential
public import LeanShared.Dynamics.SymbolicExponentialVariation

/-! The actual literal weighted potential has a cohomologous symbolic
representative with the ordinary every-radius exponential variation
property, on an actual finite-to-one Markov coding.  Original pressure
and all periodic orbit energies are preserved exactly.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Bundle IsManifold Function
open FractionalManifoldRegularity ThermodynamicDefinitions
open BilateralShadowingCoding MarkovFinitePathRealization
open scoped Topology Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

theorem BasicData.exists_weighted_exponential_potential (b : BasicData (E := E) T Λ V)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm)
    (g : M → ℝ) (weightRegular : Regular (E := E) (F := ℝ) q g)
    (weightPositive : ∀ x ∈ Λ, 0 < g x) :
    ∃ α > 0, α < 1 ∧ ∃ ψ : M → ℝ, Regular (E := E) (F := ℝ) α ψ ∧
      ∃ u : M → ℝ, Continuous u ∧
      (∀ x ∈ Λ, b.hyperbolic.potential g x = ψ x + u x - u (T x)) ∧
      pressure T (b.hyperbolic.potential g) Λ = pressure T ψ Λ ∧
      (∀ n : ℕ, ∀ x ∈ Λ, (T : M → M)^[n] x = x →
        orbitSum T (b.hyperbolic.potential g) n x = orbitSum T ψ n x) ∧
      let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
      ∃ N : ℕ, ∃ rectangles : ((Fin N ⊕ ((Fin N × Fin N) × Bool)) → Bool) → Set Λ,
        ∃ code : Path (Transition S rectangles) → Λ,
          MarkovCodingProperties S rectangles code ∧
          HasExponentialVariations (fun a => ψ (code a).val) := by
  obtain ⟨α, positiveα, smallα, ψ, regularψ, u, continuousU, same, pressureSame, periodicSame,
    N, rectangles, code, properties,
    block, positiveBlock, θ, positiveθ, smallθ, C, nonnegativeC, variation⟩ :=
    b.exists_weighted_symbolic_potential regularity weightOrder forwardRegular inverseRegular
      g weightRegular weightPositive
  exact ⟨α, positiveα, smallα, ψ, regularψ, u, continuousU, same, pressureSame, periodicSame,
    N, rectangles, code, properties,
    hasExponentialVariations_of_block (fun a => ψ (code a).val) block positiveBlock θ C
      positiveθ smallθ nonnegativeC variation⟩

end LeanShared.HyperbolicBasicSet
