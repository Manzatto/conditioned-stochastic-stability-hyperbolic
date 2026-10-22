module

public import ConditionedStochasticStabilityHyperbolic.Paper.Hypotheses
public import LeanShared.Probability.NoiseCubeRescaling
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Literal regular random perturbations from manuscript §2.4.

The map family is allowed to depend arbitrarily on ε. For each positive ε,
its ordinary extension is jointly C¹, its individual maps are genuinely C^r,
and its control derivative is surjective. A finite ordinary chart certificate
records the actual C^r Whitney bound, including the fractional top derivative.
No spectral, Banach-space or stochastic-stability conclusion is a field.
Driving laws vary freely with ε; only their positive-scale probability,
full support and bounded Lebesgue densities are required.
-/

@[expose] public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff Topology NNReal ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [Fintype ι]

abbrev Control := ι → ℝ
abbrev cube (ε : ℝ≥0) := NoiseCubeRescaling.cube (ι := ι) ε

/-- A fixed finite chart presentation of an ordinary Whitney neighborhood
of the deterministic map. Its patches cover the actual manifold. -/
structure WhitneyAtlas (T : M → M) where
  count : ℕ
  source : Fin count → OpenPartialHomeomorph M E
  target : Fin count → OpenPartialHomeomorph M E
  source_smooth : ∀ i, source i ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M
  target_smooth : ∀ i, target i ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M
  patch : Fin count → Set M
  patch_open : ∀ i, IsOpen (patch i)
  patch_cover : ⋃ i, patch i = univ
  patch_compact : ∀ i, IsCompact (closure (patch i))
  patch_source : ∀ i, closure (patch i) ⊆ (source i).source
  deterministic_target : ∀ i, T '' closure (patch i) ⊆ (target i).source

namespace WhitneyAtlas
variable {T : M → M} (A : WhitneyAtlas (E := E) T)

def coordinate (f : M → M) (i : Fin A.count) : E → E :=
  A.target i ∘ f ∘ (A.source i).symm

def coordinatePatch (i : Fin A.count) : Set E :=
  (A.source i).target ∩ (A.source i).symm ⁻¹' A.patch i

/-- A quantitative ordinary C^r-Whitney bound on the actual coordinate
maps. For nonintegral r the top derivative's two-point Hölder seminorm is
controlled, rather than replacing r by its ceiling. -/
structure Bound (r : ℝ) (f : M → M) (δ : ℝ) : Prop where
  uniform : ∀ x, dist (f x) (T x) ≤ δ
  target_control : ∀ i, f '' closure (A.patch i) ⊆ (A.target i).source
  derivatives : ∀ i k, k ≤ ⌊r⌋₊ → ∀ y ∈ A.coordinatePatch i,
    ‖iteratedFDeriv ℝ k (A.coordinate f i) y -
      iteratedFDeriv ℝ k (A.coordinate T i) y‖ ≤ δ
  holder : r ≠ (⌊r⌋₊ : ℝ) → ∀ i, ∀ y ∈ A.coordinatePatch i, ∀ z ∈ A.coordinatePatch i,
    ‖(iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate f i) y -
        iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate T i) y) -
      (iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate f i) z -
        iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate T i) z)‖ ≤
      δ * ‖y - z‖ ^ (r - (⌊r⌋₊ : ℝ))

end WhitneyAtlas

/-- The map hypotheses are independent of the choice of driving laws.
All positive-noise conclusions are local in the noise scale. -/
structure Maps (T : M ≃ₜ M) (r : ℝ) where
  window : ℝ≥0
  window_positive : 0 < window
  family : ℝ≥0 → Control (ι := ι) → M → M
  atlas : WhitneyAtlas (E := E) (T : M → M)
  constant : ℝ
  constant_positive : 0 < constant
  map_regular : ∀ ε : ℝ≥0, 0 < ε → ε ≤ window → ∀ control : cube (ι := ι) ε,
    FractionalManifoldRegularity.Regular (E := E) (F := E) r (family ε control.val)
  joint_C1 : ∀ ε : ℝ≥0, 0 < ε → ε ≤ window →
    ∃ O : Set (Control (ι := ι)), IsOpen O ∧
      (NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) ⊆ O ∧
      ContMDiffOn ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) 1
        (fun z : Control (ι := ι) × M => family ε z.1 z.2) (O ×ˢ univ)
  control_surjective : ∀ ε : ℝ≥0, 0 < ε → ε ≤ window →
    ∀ (control : cube (ι := ι) ε) (x : M),
      Function.Surjective (mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
        (fun v : Control (ι := ι) => family ε v x) control.val)
  whitney_bound : ∀ ε : ℝ≥0, 0 < ε → ε ≤ window → ∀ control : cube (ι := ι) ε,
    atlas.Bound r (family ε control.val) (constant * ‖control.val‖)

namespace Maps
variable {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)

omit [FiniteDimensional ℝ E] in
theorem uniform_close (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window)
    (control : cube (ι := ι) ε) (x : M) :
    dist (F.family ε control.val x) (T x) ≤ F.constant * (ε : ℝ) := by
  exact ((F.whitney_bound ε hε hwindow control).uniform x).trans
    (mul_le_mul_of_nonneg_left (NoiseCubeRescaling.cube_norm_le (ε : ℝ) ε.property control) F.constant_positive.le)

omit [FiniteDimensional ℝ E] in
theorem zero_control (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window) (x : M) :
    F.family ε 0 x = T x := by
  have hzero : (0 : Control (ι := ι)) ∈ (NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) := by
    intro i
    simp
  have h := (F.whitney_bound ε hε hwindow ⟨0, hzero⟩).uniform x
  simp only [norm_zero, mul_zero, dist_le_zero] at h
  exact h

end Maps

/-- Restricted ordinary Lebesgue volume on the actual control cube. -/
def cubeVolume (ε : ℝ≥0) : Measure (cube (ι := ι) ε) :=
  (volume : Measure (Control (ι := ι))).comap Subtype.val

/-- The density and full-support assumptions are required only for ε>0.
There is no continuity or convergence hypothesis on the laws. -/
structure Laws where
  law : (ε : ℝ≥0) → Measure (cube (ι := ι) ε)
  probability : ∀ ε, IsProbabilityMeasure (law ε)
  full_support : ∀ ε : ℝ≥0, 0 < ε → (law ε).IsOpenPosMeasure
  bounded_density : ∀ ε : ℝ≥0, 0 < ε →
    ∃ p : cube (ι := ι) ε → ℝ≥0∞, Measurable p ∧
      ∃ B : ℝ≥0∞, B ≠ (∞ : ℝ≥0∞) ∧ (∀ control, p control ≤ B) ∧
        law ε = (cubeVolume (ι := ι) ε).withDensity p

/-- The represented ordinary Whitney-to-map-space certificate used by the
analytic model constructor. It concerns actual maps and their topology;
it contains no transfer estimate, completed space, projector or gap. -/
structure Representation {T : M ≃ₜ M} {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (Parameters : Type*) [MetricSpace Parameters]
    (evaluate : Parameters → M → M) where
  window : ℝ≥0
  window_positive : 0 < window
  window_le : window ≤ F.window
  reference : Parameters
  reference_map : evaluate reference = T
  represent : ∀ ε : ℝ≥0, 0 < ε → ε ≤ window → cube (ι := ι) ε → Parameters
  actual_map : ∀ ε hε hwindow control, evaluate (represent ε hε hwindow control) = F.family ε control.val
  constant : ℝ
  constant_nonnegative : 0 ≤ constant
  close : ∀ ε hε hwindow control,
    dist (represent ε hε hwindow control) reference ≤ constant * (ε : ℝ)
  continuous : ∀ ε hε hwindow, Continuous (represent ε hε hwindow)

/-- Exact ordinary Palis/Whitney chart-calculus source. It turns the literal
quantitative C^r certificate into its chosen map-space realization. This
background source does not assert a stochastic stability conclusion. -/
def WhitneyRepresentationContract (Parameters : Type*) [MetricSpace Parameters]
    (evaluate : Parameters → M → M) : Prop :=
  ∀ {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r),
    (∃ reference, evaluate reference = T) →
    Nonempty (Representation F Parameters evaluate)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
