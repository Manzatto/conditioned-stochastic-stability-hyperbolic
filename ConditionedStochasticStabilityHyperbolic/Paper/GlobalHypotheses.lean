module

public import ConditionedStochasticStabilityHyperbolic.Paper.Hypotheses
public import ConditionedStochasticStabilityHyperbolic.Global.PaperStableBasin
public import LeanShared.Dynamics.HyperbolicThermodynamics
public import Mathlib.Dynamics.PeriodicPts.Defs

/-! Geometric HG1/HG2 with a chosen ordinary spectral-decomposition witness.
The classical Axiom-A spectral-decomposition theorem produces that witness;
its existence is not a noisy spectral/conditioned conclusion. Pressures and
equilibrium states have literal separated-set/entropy semantics. In
particular open forward invariance is not replaced by strict trapping. -/

@[expose] public noncomputable section
open Set Function Bundle MeasureTheory
open scoped Manifold ContDiff Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

/-- The ordinary nonwandering set, using genuine positive-time returns. -/
def nonwanderingSet (T : M → M) : Set M :=
  {x | ∀ U : Set M, IsOpen U → x ∈ U →
    ∃ n : ℕ, 0 < n ∧ ∃ y ∈ U, T^[n] y ∈ U}

structure AxiomAData (T : M ≃ₜ M) where
  hyperbolic : HyperbolicData (E := E) T (nonwanderingSet T)
  periodic_dense : closure (periodicPts (T : M → M)) = nonwanderingSet T

/-- Chosen output of the cited classical spectral decomposition. Each member
is a literal compact isolated transitive set and the family partitions NW. -/
structure SpectralDecomposition (T : M ≃ₜ M) where
  count : ℕ
  core : Fin count → Set M
  collar : Fin count → Set M
  basic : ∀ i, BasicData (E := E) T (core i) (collar i)
  disjoint : Pairwise (fun i j => Disjoint (core i) (core j))
  covering : ⋃ i, core i = nonwanderingSet T

namespace SpectralDecomposition
variable {T : M ≃ₜ M} (D : SpectralDecomposition (E := E) T)

def potential (g : M → ℝ) (i : Fin D.count) : M → ℝ :=
  (D.basic i).hyperbolic.potential g

def pressure (g : M → ℝ) (i : Fin D.count) : EReal :=
  ThermodynamicDefinitions.pressure T (D.potential g i) (D.core i)

def edge : Fin D.count → Fin D.count → Prop :=
  Global.PaperStableBasin.heteroclinicRelation T D.core

end SpectralDecomposition

variable [MeasurableSpace M] [BorelSpace M]

/-- Literal HG1, after choosing the ordinary deterministic decomposition.
No subordinate mixing, boundary-nullity or strict-trapping condition occurs. -/
structure HG1 {T : M ≃ₜ M} (D : SpectralDecomposition (E := E) T)
    (g : M → ℝ) (A : Set M) where
  r : ℝ
  regularity_gt_one : 1 < r
  map_regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r (T : M → M)
  inverse_regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r (T.symm : M → M)
  axiomA : AxiomAData (E := E) T
  absorbing_open : IsOpen A
  absorbing_forward : MapsTo T A A
  weight_regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) g
  weight_nonnegative : ∀ x, 0 ≤ g x
  weight_positive : ∀ i, D.core i ⊆ Aᶜ → ∀ x ∈ D.core i, 0 < g x
  no_cycles : ∀ i, ¬ Relation.TransGen D.edge i i
  dominant : Fin D.count
  dominant_live : D.core dominant ⊆ Aᶜ
  pressure_dominant : ∀ i, D.core i ⊆ Aᶜ → i ≠ dominant → D.pressure g i < D.pressure g dominant
  deterministic_equilibrium : EquilibriumPackage (D.basic dominant).hyperbolic g
  dominant_mixing : MixingOn T (D.core dominant)

/-- HG2 adds pressure separation and mixing on every retained basic set. -/
structure HG2 {T : M ≃ₜ M} (D : SpectralDecomposition (E := E) T)
    (g : M → ℝ) (A : Set M) extends HG1 D g A where
  pressures_distinct : ∀ i j, D.core i ⊆ Aᶜ → D.core j ⊆ Aᶜ →
    D.pressure g i = D.pressure g j → i = j
  retained_mixing : ∀ i, D.core i ⊆ Aᶜ → MixingOn T (D.core i)

end ConditionedStochasticStabilityHyperbolic.Paper
