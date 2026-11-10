module
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-!
# Local conditioned stochastic stability
The local results are Theorems 2.7 and 2.8 of arXiv:2506.15503v3.
Definitions below give the geometric, noise, conditioning and thermodynamic
meaning independently of the proof development. The chain and transfer
operator are definition holes constrained by their integral identities;
these identities are compared along with the two main results.
-/
@[expose] public noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter Bundle
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
section
namespace LeanShared

variable {X : Type*}

/-- Points whose entire forward orbit stays in `K`. -/
def forwardTrapped (f : X → X) (K : Set X) : Set X :=
  {x | ∀ n : ℕ, f^[n] x ∈ K}

/-- Points whose forward and backward orbits stay in `K`. -/
def isolatedCore [TopologicalSpace X] (T : X ≃ₜ X) (K : Set X) : Set X :=
  forwardTrapped T K ∩ forwardTrapped T.symm K
end LeanShared
end

section
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
end
end

section
@[expose] public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology Bundle
namespace LeanShared.HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

/-- Actual uniformly hyperbolic tangent data, with continuous splitting. -/
structure HyperbolicData (T : M ≃ₜ M) (Λ : Set M) where
  compact : IsCompact Λ
  invariant : T '' Λ = Λ
  stable : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x)
  unstable : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x)
  complementary : ∀ x ∈ Λ, IsCompl (stable x) (unstable x)
  projection : ∀ x : M,
    TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x
  projection_range : ∀ x ∈ Λ, (projection x).range = stable x
  projection_kernel : ∀ x ∈ Λ, (projection x).ker = unstable x
  projection_idempotent : ∀ x ∈ Λ, (projection x).comp (projection x) = projection x
  continuous_splitting : ContinuousOn
    (fun v : TangentBundle (𝓘(ℝ, E)) M =>
      (⟨v.proj, projection v.proj v.2⟩ : TangentBundle (𝓘(ℝ, E)) M))
    {v | v.proj ∈ Λ}
  stable_invariant : ∀ x ∈ Λ,
    (stable x).map (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap = stable (T x)
  unstable_invariant : ∀ x ∈ Λ,
    (unstable x).map (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap = unstable (T x)
  constant : ℝ
  contraction : ℝ
  constant_pos : 0 < constant
  contraction_pos : 0 < contraction
  contraction_lt_one : contraction < 1
  stable_bound : ∀ n : ℕ, ∀ x ∈ Λ, ∀ v ∈ stable x,
    ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T : M → M)^[n]) x v‖ ≤
      constant * contraction ^ n * ‖v‖
  unstable_bound : ∀ n : ℕ, ∀ x ∈ Λ, ∀ v ∈ unstable x,
    ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T.symm : M → M)^[n]) x v‖ ≤
      constant * contraction ^ n * ‖v‖

/-- Both time directions of the actual homeomorphism orbit. -/
def orbit (T : M ≃ₜ M) (x : M) (n : ℤ) : M :=
  if 0 ≤ n then (T : M → M)^[n.toNat] x else (T.symm : M → M)^[(-n).toNat] x

/-- The paper's compact isolated transitive basic set, without a saddle-only
restriction or a mixing condition hidden in the definition. -/
structure BasicData (T : M ≃ₜ M) (Λ V : Set M) where
  hyperbolic : HyperbolicData (E := E) T Λ
  nonempty : Λ.Nonempty
  open_neighborhood : IsOpen V
  subset_neighborhood : Λ ⊆ V
  isolated : Λ = LeanShared.isolatedCore T (closure V)
  dense_orbit : ∃ x ∈ Λ, Λ ⊆ closure (range (orbit T x))

/-- Relative open-set topological mixing, with the eventual quantifier over
all sufficiently large integer times. -/
def MixingOn (T : M ≃ₜ M) (Λ : Set M) : Prop :=
  ∀ U W : Set M, IsOpen U → IsOpen W → (Λ ∩ U).Nonempty → (Λ ∩ W).Nonempty →
    ∃ N : ℕ, ∀ n ≥ N, ∃ x ∈ Λ ∩ U, (T : M → M)^[n] x ∈ W
end LeanShared.HyperbolicBasicSet
end
end

section
attribute [local instance 2000] NormedField.toNormedSpace
@[expose] public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace LeanShared.ThermodynamicDefinitions

section Pressure
variable {X : Type*} [MetricSpace X]

def Separated (T : X → X) (K : Set X) (n : ℕ) (ε : ℝ) (s : Finset X) : Prop :=
  (∀ x ∈ s, x ∈ K) ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
    ∃ i : ℕ, i < n ∧ ε ≤ dist (T^[i] x) (T^[i] y)

def orbitSum (T : X → X) (φ : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  ∑ i ∈ Finset.range n, φ (T^[i] x)

def separatedPartitionSum (T : X → X) (φ : X → ℝ) (K : Set X) (n : ℕ) (ε : ℝ) : ℝ≥0∞ := by
  classical
  exact ⨆ s : Finset X, ⨆ (_hs : Separated T K n ε s),
    ∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T φ n x))

/-- Bowen separated-set topological pressure, as an extended real value. -/
def pressure (T : X → X) (φ : X → ℝ) (K : Set X) : EReal :=
  ⨆ ε : {ε : ℝ // 0 < ε},
    limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
      (separatedPartitionSum T φ K n ε.val).log) atTop
end Pressure

section Entropy
variable {X : Type*} [MeasurableSpace X]

/-- Finite measurable partitions of the entire state space. Null atoms are
allowed; their Shannon contribution is zero by the real-log convention. -/
structure MeasurablePartition (k : ℕ) where
  atom : Fin k → Set X
  measurable : ∀ i, MeasurableSet (atom i)
  disjoint : Pairwise (fun i j => Disjoint (atom i) (atom j))
  covering : ⋃ i, atom i = univ

def dynamicalAtom {k : ℕ} (P : MeasurablePartition (X := X) k)
    (T : X → X) (n : ℕ) (word : Fin n → Fin k) : Set X :=
  ⋂ i : Fin n, (T^[i.val]) ⁻¹' P.atom (word i)

def dynamicalEntropy {k : ℕ} (P : MeasurablePartition (X := X) k)
    (T : X → X) (μ : Measure X) (n : ℕ) : ℝ :=
  -∑ word : Fin n → Fin k,
    μ.real (dynamicalAtom P T n word) * Real.log (μ.real (dynamicalAtom P T n word))

/-- Kolmogorov–Sinai entropy via finite measurable partitions. For an
invariant probability the usual subadditivity theorem supplies the limit
in place of the liminf appearing in this definition. -/
def entropy (T : X → X) (μ : Measure X) : EReal :=
  ⨆ k : ℕ, ⨆ P : MeasurablePartition (X := X) k,
    liminf (fun n : ℕ => (((n : ℝ)⁻¹ * dynamicalEntropy P T μ n : ℝ) : EReal)) atTop
end Entropy

section Equilibrium
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The actual variational equality, with invariant probability and support
on the specified invariant set. No noisy measure occurs in this predicate. -/
def IsEquilibriumState (T : X → X) (φ : X → ℝ) (K : Set X)
    (ν : ProbabilityMeasure X) : Prop :=
  Measurable T ∧ (ν : Measure X).map T = ν ∧ (ν : Measure X) Kᶜ = 0 ∧
    Integrable φ (ν : Measure X) ∧
    entropy T ν + ((∫ x, φ x ∂(ν : Measure X) : ℝ) : EReal) = pressure T φ K

end Equilibrium
end LeanShared.ThermodynamicDefinitions
end
end

section
@[expose] public noncomputable section
open Set MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle
namespace LeanShared.HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

/-- Intrinsic volume expansion of the actual unstable tangent restriction.
Using its image as codomain works without a choice of tangent frames. -/
def HyperbolicData.unstableJacobian (h : HyperbolicData (E := E) T Λ) (x : M) : ℝ :=
  let A := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (T : M → M) x
  (A.restrict (show MapsTo A (h.unstable x) ((h.unstable x).map A.toLinearMap) from
    fun v hv => Submodule.mem_map.mpr ⟨v, hv, rfl⟩)).toLinearMap.normDet

def HyperbolicData.potential (h : HyperbolicData (E := E) T Λ) (g : M → ℝ) : M → ℝ :=
  fun x => Real.log (g x) - Real.log (h.unstableJacobian x)

variable [MeasurableSpace M] [BorelSpace M]

/-- Exact deterministic pressure/equilibrium theorem output to be discharged
by Bowen/GL/BT theory. The pressure scalar is tied to separated-set pressure,
and the state to the actual entropy-plus-potential variational equality. -/
structure EquilibriumPackage (h : HyperbolicData (E := E) T Λ) (g : M → ℝ) where
  pressure : ℝ
  pressure_identity : ThermodynamicDefinitions.pressure T (h.potential g) Λ = (pressure : EReal)
  state : ProbabilityMeasure M
  equilibrium : ThermodynamicDefinitions.IsEquilibriumState T (h.potential g) Λ state
  unique : ∀ ν, ThermodynamicDefinitions.IsEquilibriumState T (h.potential g) Λ ν → ν = state

end LeanShared.HyperbolicBasicSet
end
end

section
@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

/-- Manuscript HL, including the standing nonnegative-weight convention.
Saddle dimensions are deliberately not inserted into this hypothesis. -/
structure HL (T : M ≃ₜ M) (g : M → ℝ) (Λ V : Set M) where
  r : ℝ
  regularity_gt_one : 1 < r
  map_regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r (T : M → M)
  inverse_regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r (T.symm : M → M)
  basic : BasicData (E := E) T Λ V
  weight_regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) g
  weight_nonnegative : ∀ x, 0 ≤ g x
  weight_supported : tsupport g ⊆ V
  weight_positive : ∀ x ∈ Λ, 0 < g x
  mixing : MixingOn T Λ
end ConditionedStochasticStabilityHyperbolic.Paper
end
end

section
namespace LeanShared.NoiseCubeRescaling
variable {ι : Type*}
def cube (ε : ℝ) := {ω : ι → ℝ | ∀ i, |ω i| ≤ ε}
end LeanShared.NoiseCubeRescaling
end

section
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
namespace Laws
variable (L : Laws (ι := ι))
instance law_probability (ε : ℝ≥0) : IsProbabilityMeasure (L.law ε) := L.probability ε
end Laws
namespace Maps
variable {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
variable [MeasurableSpace M] [BorelSpace M]
omit [FiniteDimensional ℝ E] in
/-- Jointly measurable random update on each positive control cube. -/
theorem raw_measurable (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window) :
    Measurable (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1) := by sorry
end Maps
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
end
end

section
namespace AbsorbingMarkovChains
variable {M : Type*} [MeasurableSpace M]
/-- The coproduct sigma algebra on the live states and one cemetery point. -/
instance optionStateMeasurableSpace : MeasurableSpace (Option M) :=
  (inferInstance : MeasurableSpace M).map Option.some

@[fun_prop]
theorem measurable_some_state : Measurable (Option.some : M → Option M) :=
  Measurable.of_le_map le_rfl
/-- A genuine probability transition kernel with an absorbing cemetery. -/
structure CanonicalChain (M : Type*) [MeasurableSpace M] where
  transition : Kernel (Option M) (Option M)
  markov : IsMarkovKernel transition
  absorbing : transition none = Measure.dirac none

attribute [instance] CanonicalChain.markov

namespace CanonicalChain

/-- Canonical coordinate paths, equipped with the product sigma algebra. -/
abbrev Path (M : Type*) := ℕ → Option M

variable (C : CanonicalChain M)

/-- The next-step kernel reads the most recent coordinate of a finite history. -/
def historyKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Option M) (Option M) :=
  C.transition.comap (fun ω => ω ⟨n, by simp⟩) (measurable_pi_apply _)

instance historyKernel_isMarkov (n : ℕ) : IsMarkovKernel (C.historyKernel n) := by
  unfold historyKernel
  infer_instance
/-- Path law obtained by starting at the live state `x` and iterating `transition`. -/
def pathMeasure (x : M) : Measure (Path M) :=
  Kernel.trajMeasure (Measure.dirac (some x)) C.historyKernel
variable {C}
/-- Survival through time `n`, including time zero. -/
def survival (n : ℕ) : Set (Path M) :=
  {ω | ∀ k : ℕ, k ≤ n → ω k ≠ none}
def conditionedMeasure (x : M) (n : ℕ) : Measure (Path M) :=
  ProbabilityTheory.cond (C.pathMeasure x) (survival n)
end CanonicalChain
/-- Extend an observable by zero at the cemetery. -/
def zeroExtension (f : M → ℝ) : Option M → ℝ
  | none => 0
  | some x => f x
/-- Sum over observation times `0, ..., n - 1`. -/
def birkhoffSum (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, u i
/-- The paper's Birkhoff sum as an actual measurable function on canonical paths. -/
def pathBirkhoffSum (f : M → ℝ) (n : ℕ) (ω : CanonicalChain.Path M) : ℝ :=
  birkhoffSum (fun k => zeroExtension f (ω k)) n
end AbsorbingMarkovChains
end

section
namespace AbsorbingMarkovChains
variable {M : Type*} [MeasurableSpace M]
/-- The inclusion of live states is a measurable embedding for the chosen
coproduct sigma algebra on `Option M`. -/
theorem measurableEmbedding_some_state :
    MeasurableEmbedding (Option.some : M → Option M) where
  injective := fun _ _ h => Option.some.inj h
  measurable := measurable_some_state
  measurableSet_image' := by
    intro A hA
    change MeasurableSet (Option.some ⁻¹' (Option.some '' A))
    have heq : Option.some ⁻¹' (Option.some '' A) = A := by
      ext x
      simp
    rwa [heq]

namespace CanonicalChain

variable (C : CanonicalChain M)

/-- The transition kernel before absorption, defined from the actual
cemetery-state transition kernel. -/
def killedTransition : Kernel M M :=
  (C.transition.comap Option.some measurable_some_state).comapRight
    measurableEmbedding_some_state
end CanonicalChain
end AbsorbingMarkovChains
end

section
namespace AbsorbingMarkovChains.CanonicalChain
variable {M : Type*} [MeasurableSpace M] (C : CanonicalChain M)
/-- The manuscript's quasi-ergodic property, using the actual canonical path
law and its survival conditioning. -/
def IsQuasiErgodic (ν : Measure M) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ f : M → ℝ, Measurable f →
    (∃ B : ℝ, ∀ y, |f y| ≤ B) → ∀ᵐ x ∂ν,
      Tendsto (fun n : ℕ => ∫ ω, (n : ℝ)⁻¹ * pathBirkhoffSum f n ω
        ∂C.conditionedMeasure x n) atTop (𝓝 (∫ y, f y ∂ν))
end AbsorbingMarkovChains.CanonicalChain
end

section
namespace ConditionedStochasticStabilityHyperbolic
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
/-- The usual strong-Feller property for the real bounded-measurable kernel
integral. No regularity of the density or operator-norm continuity is assumed. -/
def HasStrongFellerKernel (C : AbsorbingMarkovChains.CanonicalChain X) : Prop :=
  ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖f y‖ ≤ B) →
    Continuous (fun x => ∫ y, f y ∂C.killedTransition x)
end ConditionedStochasticStabilityHyperbolic
namespace ConditionedStochasticStabilityHyperbolic
/-- The continuous killed transfer operator, fixed by the following identity. -/
def strongFellerTransferOperator {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (C : AbsorbingMarkovChains.CanonicalChain X)
    (hSF : HasStrongFellerKernel C) : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ) := by sorry
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
/-- Its action is exactly integration against the killed transition. -/
theorem strongFellerTransferOperator_represents (f : X →ᵇ ℝ) (x : X) :
    strongFellerTransferOperator C hSF f x = ∫ y, f y ∂C.killedTransition x := by sorry
end ConditionedStochasticStabilityHyperbolic
end

section
namespace LeanShared
variable {X : Type*} [MeasurableSpace X]
/-- The product measure `g μ`, without requiring the eigenmeasure to have mass one. -/
def eigenvectorMeasure (μ : Measure X) (g : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (g x))
end LeanShared
end

section
namespace LeanShared.SubtypeKernel
variable {X : Type*}
def zeroExtend (U : Set X) (f : U → ℝ) : X → ℝ :=
  Function.extend Subtype.val f (fun _ => 0)

end LeanShared.SubtypeKernel
end

section
namespace ConditionedStochasticStabilityHyperbolic.RestrictedNoise
open AbsorbingMarkovChains
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
  (U : Set X) (hU : MeasurableSet U)
/-- The chain killed outside U with departure weight w/R, fixed by integral_chain. -/
def chain (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
    (U : Set X) (hU : MeasurableSet U) (w : U → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) : CanonicalChain U := by sorry
/-- The killed transition is the weighted random update restricted to U. -/
theorem integral_chain (w : U → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (f : U → ℝ) (hf : Measurable f) (x : U) :
    (∫ y, f y ∂(chain ρ F hF U hU w hw R hR hwR).killedTransition x) =
      (w x / R) * ∫ ω, U.indicator (LeanShared.SubtypeKernel.zeroExtend U f)
        (F (x.val, ω)) ∂ρ := by sorry
end ConditionedStochasticStabilityHyperbolic.RestrictedNoise
end

section
@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- The full spectral/product conclusion, including the finite left measure
and the normalization, rather than only existence of a QEM. -/
structure SpectralWitness (C : AbsorbingMarkovChains.CanonicalChain X)
    (R : ℝ) (ν : ProbabilityMeasure X) where
  strongFeller : HasStrongFellerKernel C
  eigenfunction : X →ᵇ ℝ
  eigenfunction_nonnegative : ∀ x, 0 ≤ eigenfunction x
  eigenmeasure : Measure X
  finite_eigenmeasure : IsFiniteMeasure eigenmeasure
  rate : ℝ
  rate_positive : 0 < rate
  right : (R • strongFellerTransferOperator C strongFeller) eigenfunction =
    rate • eigenfunction
  left : ∀ f : X →ᵇ ℝ,
    (∫ x, ((R • strongFellerTransferOperator C strongFeller) f) x ∂eigenmeasure) =
      rate * ∫ x, f x ∂eigenmeasure
  normalization : ∫ x, eigenfunction x ∂eigenmeasure = 1
  product : (ν : Measure X) = eigenvectorMeasure eigenmeasure eigenfunction
  radius : spectralRadius ℝ (R • strongFellerTransferOperator C strongFeller) =
    ENNReal.ofReal rate

/-- Qualified uniqueness is exactly the qualification in thm:qem-local.
The QEM definition quantifies over every bounded measurable observable. -/
def Point (C : AbsorbingMarkovChains.CanonicalChain X) (R : ℝ)
    (core : Set X) (ν : ProbabilityMeasure X) : Prop :=
  C.IsQuasiErgodic (ν : Measure X) ∧ core ⊆ (ν : Measure X).support ∧
    (∀ ζ : Measure X, C.IsQuasiErgodic ζ → core ⊆ ζ.support → ζ = (ν : Measure X)) ∧
    Nonempty (SpectralWitness C R ν)

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}
  (F : RegularNoise.Maps (E := E) (ι := ι) T r) (L : RegularNoise.Laws (ι := ι))
  (K Λ : Set M) [CompactSpace K] (hK : MeasurableSet K)
  (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)

/-- The local existence theorem with one positive window chosen before
initial states and observables. The chain is the literal original law. -/
def Existence : Prop :=
  ∃ δ : ℝ≥0, ∃ hwindow : δ ≤ F.window, 0 < δ ∧
    ∃ ν : ℝ≥0 → ProbabilityMeasure K, ∀ ε : ℝ≥0, (hε : 0 < ε) → (hδ : ε ≤ δ) →
      Point (RestrictedNoise.chain (L.law ε)
        (fun z : M × RegularNoise.cube (ι := ι) ε => F.family ε z.2.val z.1)
        (F.raw_measurable ε hε (hδ.trans hwindow)) K hK w hw R hR hwR)
        R {x : K | x.val ∈ Λ} (ν ε)
/-- The second local theorem uses the same QEM family and the genuine
entropy/pressure equilibrium definition. The limit on K pushes forward to
the equilibrium state on M; no equilibrium property is replaced by a name. -/
def Stability (potential : M → ℝ) : Prop :=
  ∃ ν₀ : ProbabilityMeasure K, ∃ νeq : ProbabilityMeasure M,
    (ν₀ : Measure K).map Subtype.val = (νeq : Measure M) ∧
    ThermodynamicDefinitions.IsEquilibriumState T potential Λ νeq ∧
    (∀ ζ : ProbabilityMeasure M,
      ThermodynamicDefinitions.IsEquilibriumState T potential Λ ζ → ζ = νeq) ∧
    ∃ δ : ℝ≥0, ∃ hwindow : δ ≤ F.window, 0 < δ ∧
      ∃ ν : ℝ≥0 → ProbabilityMeasure K,
        Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) ∧
        ∀ ε : ℝ≥0, (hε : 0 < ε) → (hδ : ε ≤ δ) →
          Point (RestrictedNoise.chain (L.law ε)
            (fun z : M × RegularNoise.cube (ι := ι) ε => F.family ε z.2.val z.1)
            (F.raw_measurable ε hε (hδ.trans hwindow)) K hK w hw R hR hwR)
            R {x : K | x.val ∈ Λ} (ν ε)
end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
end
end

section
public noncomputable section
open Set Function MeasureTheory Filter IsManifold Bundle
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic
open LeanShared HyperbolicBasicSet Paper Paper.RegularNoise

section Local

variable {X E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  {ι : Type} [Fintype ι] {T : X ≃ₜ X} {g : X → ℝ} {Λ V : Set X}

local instance mainCompactClosure (W : Set X) : CompactSpace (closure W) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

/-- **Theorem 2.7** (`thm:qem-local`). Under Hypothesis (HL), for every small noise scale `ε` the
process on `V̄` weighted by `e^φ` and killed outside `V̄` has a quasi-ergodic measure `ν_ε` with
`Λ ⊆ supp ν_ε`, unique among quasi-ergodic measures whose support contains `Λ`, and
`ν_ε = μ_ε(· g_ε)` for the leading eigenfunction `g_ε` and eigenmeasure `μ_ε` of `P_ε`, whose
eigenvalue is the spectral radius on `C⁰(V̄)`. The weight `e^φ ∈ C^{r-1}(V̄)` is given as the
restriction of a nonnegative `C^{r-1}` function `w` on `M` equal to `g` on `Λ`. -/
theorem Theorem2_7 (h : HL (E := E) T g Λ V)
    (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
    (w : X → ℝ) (hwRegular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) w)
    (hw0 : ∀ x, 0 ≤ w x) (agree : EqOn w g Λ)
    (φ : X → ℝ) (weight_exp : ∀ x : closure V, w x.val = Real.exp (φ x.val)) :
    ∃ (hwExp : Continuous (fun x : closure V => Real.exp (φ x.val)))
      (R : ℝ) (hR : 0 < R) (bound : ∀ x : closure V, Real.exp (φ x.val) ≤ R),
      LocalConclusions.Existence P L (closure V) Λ isClosed_closure.measurableSet
        (fun x => Real.exp (φ x.val)) hwExp.measurable R hR bound := by sorry

/-- **Theorem 2.8** (`thm:local`). The quasi-ergodic measures `ν_ε` of Theorem 2.7 converge
weakly, as `ε → 0⁺`, to the unique equilibrium state of `φ - log |det DT|_{E^u}|` on `Λ`. -/
theorem Theorem2_8 (h : HL (E := E) T g Λ V)
    (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
    (w : X → ℝ) (hwRegular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) w)
    (hw0 : ∀ x, 0 ≤ w x) (agree : EqOn w g Λ)
    (φ : X → ℝ) (weight_exp : ∀ x : closure V, w x.val = Real.exp (φ x.val)) :
    ∃ (hwExp : Continuous (fun x : closure V => Real.exp (φ x.val)))
      (R : ℝ) (hR : 0 < R) (bound : ∀ x : closure V, Real.exp (φ x.val) ≤ R),
      LocalConclusions.Stability P L (closure V) Λ isClosed_closure.measurableSet
        (fun x => Real.exp (φ x.val)) hwExp.measurable R hR bound
        (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) := by sorry

end Local
end ConditionedStochasticStabilityHyperbolic
end
end
