module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring

/-! Actual fractional C^r regularity in smooth manifold charts.

For nonintegral r=m+α this requires C^m and a local, two-point α-Hölder
bound on the actual mth chart derivative. Integral r uses ordinary C^m.
This is stronger than pointwise Hölder regularity and does not round r up
to an integer or ask for continuity in the highest Hölder norm of a family.
The charts are the given boundaryless smooth manifold charts. -/

@[expose] public noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

def chartMap (f : M → N) (x : M) : E → F :=
  extChartAt (𝓘(ℝ, F)) (f x) ∘ f ∘ (extChartAt (𝓘(ℝ, E)) x).symm

def chartDomain (f : M → N) (x : M) : Set E :=
  (extChartAt (𝓘(ℝ, E)) x).target ∩
    (extChartAt (𝓘(ℝ, E)) x).symm ⁻¹' (f ⁻¹' (extChartAt (𝓘(ℝ, F)) (f x)).source)

/-- The full two-point Hölder condition on a coordinate neighborhood, not
just the pointwise estimate with one point fixed. -/
def HolderDerivativeAt (r : ℝ) (f : M → N) (x : M) : Prop :=
  ∃ U : Set E, IsOpen U ∧ extChartAt (𝓘(ℝ, E)) x x ∈ U ∧
    U ⊆ chartDomain (E := E) (F := F) f x ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ z ∈ U,
      ‖iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E := E) (F := F) f x) y -
        iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E := E) (F := F) f x) z‖ ≤
        C * ‖y - z‖ ^ (r - (⌊r⌋₊ : ℝ))

/-- The ordinary real-indexed C^r class used by the manuscript. -/
structure Regular (r : ℝ) (f : M → N) : Prop where
  nonnegative : 0 ≤ r
  differentiable : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) (⌊r⌋₊ : ℕ) f
  holder : r ≠ (⌊r⌋₊ : ℝ) → ∀ x, HolderDerivativeAt (E := E) (F := F) r f x

/-- A certificate of the ordinary neighborhood-extension interpretation of
C^r on a closed live set. This certificate is separate from HL and is
discharged by a classical extension/cutoff source when that interpretation
is needed; no extension is inferred merely from continuity on the set. -/
def HasRegularExtensionOn (r : ℝ) (f : M → N) (K : Set M) : Prop :=
  ∃ g : M → N, Regular (E := E) (F := F) r g ∧ EqOn g f K

end LeanShared.FractionalManifoldRegularity
