module

public import LeanShared.Dynamics.BasicHyperbolicMarkovObservableVariation
public import LeanShared.Dynamics.BasicHyperbolicRegularPotentialRepresentative
public import LeanShared.Dynamics.ContinuousCoreCoboundary

/-! A literal positive regular transfer weight produces a symbolic
potential with exponential cylinder variations on the actual finite-to-one
Markov coding.  Its core coboundary, exact periodic energies and original
supplied-metric pressure are retained.  No weighted zeta theorem is
assumed or asserted by this construction.
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

theorem BasicData.exists_weighted_symbolic_potential (b : BasicData (E := E) T Λ V)
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
          ∃ block : ℕ, 0 < block ∧ ∃ θ > 0, θ < 1 ∧ ∃ C ≥ 0,
            ∀ n : ℕ, ∀ a a' : Path (Transition S rectangles),
              (∀ k : ℤ, -((block * n : ℕ) : ℤ) ≤ k → k ≤ (block * n : ℕ) → a.val k = a'.val k) →
              |ψ (code a').val - ψ (code a).val| ≤ C * θ ^ n := by
  obtain ⟨α, positiveα, smallα, ψ, regularψ, u, continuousU, same⟩ :=
    b.exists_regular_potential_representative regularity weightOrder forwardRegular inverseRegular
      g weightRegular weightPositive
  have one : 1 ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using regularity.le)
  have forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T :=
    forwardRegular.differentiable.of_le (by exact_mod_cast one)
  have inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm :=
    inverseRegular.differentiable.of_le (by exact_mod_cast one)
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  have pressureSame := pressure_continuous_core_coboundary T Λ b.hyperbolic.compact invariant
    (b.hyperbolic.potential g) ψ u continuousU.continuousOn same
  have periodicSame (n : ℕ) (x : M) (inside : x ∈ Λ) (fixed : (T : M → M)^[n] x = x) :
      orbitSum T (b.hyperbolic.potential g) n x = orbitSum T ψ n x := by
    have identity := orbitSum_coboundary invariant same n inside
    simpa only [fixed, add_sub_cancel_right] using identity
  exact ⟨α, positiveα, smallα, ψ, regularψ, u, continuousU, same, pressureSame, periodicSame,
    b.exists_markov_observable_variation forward inverse ψ α positiveα smallα regularψ⟩

end LeanShared.HyperbolicBasicSet
