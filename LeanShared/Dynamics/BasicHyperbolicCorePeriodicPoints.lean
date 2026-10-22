module

public import LeanShared.Dynamics.BasicHyperbolicPeriodicPartition
public import LeanShared.Dynamics.InvariantCoreHomeomorphism
public import LeanShared.Dynamics.PressureInvariantSubtype

/-! The actual finite ambient periodic point sets restrict exactly to
the invariant core.  Their literal weighted sums are the original
BasicData periodic partition sums, with the original ambient potential.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
open ThermodynamicDefinitions
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

@[expose] def BasicData.corePeriodicPoints (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (n : ℕ) (positive : 0 < n) : Finset Λ := by
  classical
  exact (b.periodicPoints forward inverse n positive).subtype (fun x => x ∈ Λ)

theorem BasicData.mem_corePeriodicPoints (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (n : ℕ) (positive : 0 < n) (x : Λ) :
    x ∈ b.corePeriodicPoints forward inverse n positive ↔
      (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant : Λ → Λ)^[n] x = x := by
  classical
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  have forwardS (y : Λ) : (S y).val = T y.val := rfl
  rw [corePeriodicPoints, Finset.mem_subtype, b.mem_periodicPoints forward inverse n positive]
  constructor
  · intro h
    apply Subtype.ext
    exact (iterate_coe_restriction S forwardS n x).trans h.2
  · intro h
    refine ⟨x.property, ?_⟩
    have coordinate := congrArg (fun y : Λ => y.val) h
    rw [iterate_coe_restriction S forwardS] at coordinate
    exact coordinate

theorem BasicData.core_periodic_weight_sum (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (ψ : M → ℝ) (n : ℕ) (positive : 0 < n) :
    (∑ x ∈ b.corePeriodicPoints forward inverse n positive,
      Real.exp (orbitSum (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant)
        (fun y => ψ y.val) n x)) = b.periodicPartitionSum forward inverse ψ n := by
  classical
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  have forwardS (x : Λ) : (S x).val = T x.val := rfl
  rw [b.periodicPartitionSum_eq forward inverse ψ n positive, corePeriodicPoints]
  change (∑ x ∈ (b.periodicPoints forward inverse n positive).subtype (fun x => x ∈ Λ),
      Real.exp (orbitSum S (fun y => ψ y.val) n x)) = _
  simp_rw [orbitSum_restriction S forwardS ψ]
  exact Finset.sum_subtype_of_mem (p := fun x => x ∈ Λ)
    (fun x : M => Real.exp (orbitSum T ψ n x))
    (fun x hx => ((b.mem_periodicPoints forward inverse n positive x).mp hx).1)

end LeanShared.HyperbolicBasicSet
