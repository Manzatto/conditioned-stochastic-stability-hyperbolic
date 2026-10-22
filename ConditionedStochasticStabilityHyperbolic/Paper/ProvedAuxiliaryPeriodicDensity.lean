module

public import ConditionedStochasticStabilityHyperbolic.Paper.AuxiliaryAnosov
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductNonwandering
public import LeanShared.Dynamics.BasicHyperbolicPeriodicDensity

/-! Full-manifold HL data construct their periodic density and Axiom-A certificate. -/
public noncomputable section
open Set Function Bundle MeasureTheory
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}

/-- Literal HL regularity and mixing prove periodic density on its core. -/
theorem HL.closure_periodic_inter_core (h : HL (E := E) T g Λ V) :
    closure (Λ ∩ periodicPts (T : M → M)) = Λ := by
  have oneFloor : (1 : ℕ) ≤ ⌊h.r⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using h.regularity_gt_one.le)
  exact h.basic.closure_periodic_inter_core
    (h.map_regular.differentiable.of_le (by exact_mod_cast oneFloor))
    (h.inverse_regular.differentiable.of_le (by exact_mod_cast oneFloor)) h.mixing

theorem HL.closure_periodic_eq_univ (h : HL (E := E) T g univ V) :
    closure (periodicPts (T : M → M)) = univ := by
  simpa only [univ_inter] using h.closure_periodic_inter_core

/-- A full-core HL system has no additional wandering points. -/
theorem HL.nonwandering_eq_univ (h : HL (E := E) T g univ V) :
    nonwanderingSet (T : M → M) = univ := by
  apply Subset.antisymm (subset_univ _)
  rw [← h.closure_periodic_eq_univ]
  exact closure_minimal (ProductNonwandering.periodic_subset T)
    (ProductNonwandering.nonwandering_closed T)

/-- The full-manifold Axiom-A source is constructed from HL, without a
separate periodic-density or nonwandering-set assumption. -/
@[expose] def HL.axiomA_of_full_core (h : HL (E := E) T g univ V) : AxiomAData (E := E) T where
  hyperbolic := by
    rw [h.nonwandering_eq_univ]
    exact h.basic.hyperbolic
  periodic_dense := h.closure_periodic_eq_univ.trans h.nonwandering_eq_univ.symm

section Auxiliary
variable {F Y ι : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y] [CompactSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [IsContinuousRiemannianBundle F (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MeasurableSpace Y] [BorelSpace Y] [Fintype ι]

/-- This constructor fills the `periodic_dense` field by a theorem.
It leaves the actual map and its ordinary pressure/noise data explicit. -/
@[expose] def AuxiliaryAnosov.of_full_hl {r : ℝ} (T : Y ≃ₜ Y)
    (h : HL (E := F) T (fun _ => 1) univ univ) (regularity : h.r = r)
    (stable_positive : ∀ y, 0 < Module.finrank ℝ (h.basic.hyperbolic.stable y))
    (unstable_positive : ∀ y, 0 < Module.finrank ℝ (h.basic.hyperbolic.unstable y))
    (equilibrium : EquilibriumPackage h.basic.hyperbolic (fun _ => 1))
    (pressure_zero : equilibrium.pressure = 0)
    (noise : RegularNoise.Maps (E := F) (ι := ι) T r)
    (laws : RegularNoise.Laws (ι := ι)) : AuxiliaryAnosov (F := F) (Y := Y) (ι := ι) r where
  map := T
  hl := h
  regularity := regularity
  stable_positive := stable_positive
  unstable_positive := unstable_positive
  periodic_dense := h.closure_periodic_eq_univ
  equilibrium := equilibrium
  pressure_zero := pressure_zero
  noise := noise
  laws := laws

end Auxiliary
end ConditionedStochasticStabilityHyperbolic.Paper
