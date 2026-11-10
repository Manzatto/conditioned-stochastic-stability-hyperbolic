module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Dynamics.PeriodicPts.Defs
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
# Global conditioned limits (Theorem 6.5)
Geometric hypotheses, the literal killed process, compatible filtration data,
and all four conditioned-limit clauses are specified independently below.
The theorem packages the original constructed filtration and probability
families as existential witnesses, without exposing auxiliary proof systems.
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
variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M] [ChartedSpace E M]
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
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
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
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
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
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
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
namespace ConditionedStochasticStabilityHyperbolic.Global.PaperStableBasin
open Metric
variable {X : Type*} [MetricSpace X]
def stableBasin (T : X → X) (Γ : Set X) : Set X :=
  {x | Γ.Nonempty ∧ Tendsto (fun n : ℕ => infDist (T^[n] x) Γ) atTop (𝓝 0)}
/-- The unstable basin is the stable basin for the inverse homeomorphism. -/
def unstableBasin (T : X ≃ₜ X) (Γ : Set X) : Set X := stableBasin T.symm Γ
/-- An actual heteroclinic point lies outside both basic sets. -/
def heteroclinicRelation {I : Type*} (T : X ≃ₜ X) (Λ : I → Set X)
    (i j : I) : Prop :=
  ∃ x : X, x ∈ unstableBasin T (Λ i) \ Λ i ∧ x ∈ stableBasin T (Λ j) \ Λ j
end ConditionedStochasticStabilityHyperbolic.Global.PaperStableBasin
end
section
@[expose] public noncomputable section
open Set Function Bundle MeasureTheory
open scoped Manifold ContDiff Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
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
end
end
section
@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
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
end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
end
end
section
@[expose] public noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
structure SimpleSpectralWitness (C : AbsorbingMarkovChains.CanonicalChain X)
    (R : ℝ) (ν : ProbabilityMeasure X) extends SpectralWitness C R ν where
  right_unique : ∀ f : X →ᵇ ℝ,
    (R • strongFellerTransferOperator C strongFeller) f = rate • f →
      ∃ c : ℝ, f = c • eigenfunction
  left_unique : ∀ (μ : Measure X) [IsFiniteMeasure μ],
    (∀ f : X →ᵇ ℝ,
      (∫ x, ((R • strongFellerTransferOperator C strongFeller) f) x ∂μ) =
        rate * ∫ x, f x ∂μ) →
    μ = ENNReal.ofReal (∫ x, eigenfunction x ∂μ) • eigenmeasure
end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
end
end
section
namespace LeanShared.NoiseCubeRescaling
variable {ι : Type*} [Fintype ι]
def rescale (ε : ℝ) (hε : 0 < ε) : cube (ι := ι) 1 ≃ₜ cube (ι := ι) ε where
  toFun ω := ⟨fun i => ε * ω.val i, fun i => by
    rw [abs_mul, abs_of_pos hε]
    simpa using mul_le_mul_of_nonneg_left (ω.property i) hε.le⟩
  invFun ω := ⟨fun i => ε⁻¹ * ω.val i, fun i => by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
    simpa [ne_of_gt hε] using mul_le_mul_of_nonneg_left (ω.property i) (inv_nonneg.mpr hε.le)⟩
  left_inv ω := by ext i; change ε⁻¹ * (ε * ω.val i) = ω.val i; field_simp
  right_inv ω := by ext i; change ε * (ε⁻¹ * ω.val i) = ω.val i; field_simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_const.mul
      ((continuous_apply i).comp (continuous_subtype_val : Continuous (fun ω : cube (ι := ι) 1 => ω.val)))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_const.mul
      ((continuous_apply i).comp (continuous_subtype_val : Continuous (fun ω : cube (ι := ι) ε => ω.val)))
end LeanShared.NoiseCubeRescaling
end
section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
abbrev FixedControl := NoiseCubeRescaling.cube (ι := ι) 1
namespace Maps
variable {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
def fixedMap (ε : ℝ≥0) (x : M) (z : FixedControl (ι := ι)) : M :=
  if hε : 0 < ε then F.family ε ((NoiseCubeRescaling.rescale (ε : ℝ) hε) z).val x
  else T x
end Maps
namespace ActualOriginalGlobalChain
variable [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}
def fixedRawMap (F : Maps (E := E) (ι := ι) T r) (ε : ℝ≥0) :
    M × FixedControl (ι := ι) → M :=
  if _small : 0 < ε ∧ ε ≤ F.window then fun z => F.fixedMap ε z.1 z.2 else fun z => T z.1
end ActualOriginalGlobalChain
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
end
section
namespace LeanShared
variable {X : Type*} [TopologicalSpace X]
def shiftedFiltration (T : X ≃ₜ X) (N : ℕ) (A : Set X) (M : ℕ → Set X) (i : ℕ) : Set X :=
  if i = 0 then A else (T : X → X)^[N] ⁻¹' M i
/-- Layer `i` lies between filtration levels `i` and `i+1`. -/
def filtrationLayer (M : ℕ → Set X) (i : ℕ) : Set X := M (i + 1) \ M i
end LeanShared
namespace LeanShared
variable {X : Type*}
/-- The orbit obtained by applying the map `F n` at time `n`. -/
def nonautonomousOrbit (F : ℕ → X → X) (x : X) : ℕ → X
  | 0 => x
  | n + 1 => F n (nonautonomousOrbit F x n)
end LeanShared
end
section
namespace ConditionedStochasticStabilityHyperbolic.Global.PressureFiltrationSource
set_option linter.auxLemma false in
/-- Explicit source name for the reversed list-index bound. -/
theorem reversedVertex._proof_2.{u_1} {I : Type u_1} (L : List I) (i : Fin L.length) :
    L.length - 1 - i.val < L.length := by sorry
open Lean in
set_option linter.auxLemma false in
run_cmd do
  let n := ``ConditionedStochasticStabilityHyperbolic.Global.PressureFiltrationSource.reversedVertex._proof_2
  let ci ← getConstInfo n
  let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }
  modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun s =>
    { s with lemmas := s.lemmas.insert key (n, ci.levelParams) }
variable {X I : Type*} [MetricSpace X]
def reversedVertex (L : List I) (i : Fin L.length) : I :=
  L.get ⟨L.length - 1 - i.val, by omega⟩
end ConditionedStochasticStabilityHyperbolic.Global.PressureFiltrationSource
end
section
namespace ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry
open Relation Function PressureFiltrationSource
variable {I : Type*} [DecidableEq I]
/-- All indices are literal prefixes of one derived finite order. -/
structure Data (edge : I → I → Prop) (pressure : I → ℝ) where
  order : List I
  cover : ∀ v : I, v ∈ order
  nodup : order.Nodup
  topological : ∀ i j : Fin order.length, edge (order.get i) (order.get j) → i < j
  number : ℕ
  number_positive : Nonempty I → 0 < number
  size : Fin number → ℕ
  size_positive : ∀ s, 0 < size s
  size_le : ∀ s, size s ≤ order.length
  root : ∀ s, Fin (size s)
  pressure_gap : ∀ s (i : Fin (size s)), i ≠ root s →
    pressure (reversedVertex order ⟨i.val, lt_of_lt_of_le i.isLt (size_le s)⟩) <
      pressure (reversedVertex order ⟨(root s).val, lt_of_lt_of_le (root s).isLt (size_le s)⟩)
  root_above_later : ∀ s q : Fin number, s < q → size q ≤ (root s).val
  assignment : ∀ j : Fin order.length, ∃ s : Fin number, ∃ i : Fin (size s),
    j.val = i.val ∧
    ReflTransGen (fun a b : Fin (size s) => edge
      (reversedVertex order ⟨a.val, lt_of_lt_of_le a.isLt (size_le s)⟩)
      (reversedVertex order ⟨b.val, lt_of_lt_of_le b.isLt (size_le s)⟩)) i (root s)
end ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry
end
section
namespace ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Basins
set_option linter.auxLemma false in
/-- Explicit source name for inclusion in the original finite index set. -/
theorem originalIndex._proof_2 {ℓ : ℕ} {k : Fin ℓ} (i : Fin (k.val + 1)) : i.val < ℓ := by sorry
open Lean in
set_option linter.auxLemma false in
run_cmd do
  let n := ``ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Basins.originalIndex._proof_2
  let ci ← getConstInfo n
  let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }
  modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun s =>
    { s with lemmas := s.lemmas.insert key (n, ci.levelParams) }
abbrev originalIndex {ℓ : ℕ} {k : Fin ℓ} (i : Fin (k.val + 1)) : Fin ℓ :=
  ⟨i.val, by have h := i.isLt; have hh := k.isLt; omega⟩
end ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Basins
namespace ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry.Data
open DerivedHG2Basins
set_option linter.auxLemma false in
/-- Explicit source name for the final vertex of a selected prefix. -/
theorem terminal._proof_2.{u_1} {I : Type u_1} {edge : I → I → Prop} {pressure : I → ℝ}
    (d : GreedyPrefixGeometry.Data edge pressure) (s : Fin d.number) :
    d.size s - 1 < d.order.length := by sorry
open Lean in
set_option linter.auxLemma false in
run_cmd do
  let n := ``ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry.Data.terminal._proof_2
  let ci ← getConstInfo n
  let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }
  modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun s =>
    { s with lemmas := s.lemmas.insert key (n, ci.levelParams) }
variable {I : Type*} {edge : I → I → Prop} {pressure : I → ℝ}
  (d : GreedyPrefixGeometry.Data edge pressure)
def terminal (s : Fin d.number) : Fin d.order.length :=
  ⟨d.size s - 1, by have hp := d.size_positive s; have hb := d.size_le s; omega⟩
theorem terminal_size (s : Fin d.number) : (d.terminal s).val + 1 = d.size s := by
  dsimp only [terminal]
  have hp := d.size_positive s
  omega
def selectedRoot (s : Fin d.number) : Fin ((d.terminal s).val + 1) :=
  Fin.cast (d.terminal_size s).symm (d.root s)
end ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry.Data
end
section
namespace ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry
open LeanShared
variable {X I : Type*} [MetricSpace X]
/-- Classical adapted-filtration source, for a chosen compatible enumeration.
Smooth boundaries and their nullity are recorded separately below. -/
structure AdaptedSource (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ) where
  levels : ℕ → Set X
  index : Fin ℓ → I
  zero : levels 0 = A
  monotone : Monotone levels
  absorbing_forward : MapsTo T A A
  compact_positive : ∀ i, 0 < i → i ≤ ℓ → IsCompact (levels i)
  adapted_positive : ∀ i, 0 < i → i ≤ ℓ → MapsTo T (levels i) (interior (levels i))
  terminal : levels ℓ = univ
  literal_core : ∀ i : Fin ℓ, isolatedCore T (filtrationLayer levels i.val) = Λ (index i)
variable (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ)
def levels : ℕ → Set X := shiftedFiltration T N A D.levels
end ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry
end
section
namespace ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Application
open ShiftedFiltrationGeometry
variable {X I : Type*} [MetricSpace X]
abbrev actualPrefix (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : Fin ℓ) (N : ℕ) := levels T A Λ ℓ N D (k.val + 1)
end ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Application
end
section
namespace ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies
set_option linter.auxLemma false in
/-- Explicit source name for a selected root viewed in the original index set. -/
theorem selectedIndex._proof_2 (ℓ t : ℕ) (terminal : Fin t → Fin ℓ)
    (root : ∀ s, Fin ((terminal s).val + 1)) (s : Fin t) : (root s).val < ℓ := by sorry
open Lean in
set_option linter.auxLemma false in
run_cmd do
  let n := ``ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies.selectedIndex._proof_2
  let ci ← getConstInfo n
  let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }
  modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun s =>
    { s with lemmas := s.lemmas.insert key (n, ci.levelParams) }
variable (ℓ t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
abbrev selectedIndex (s : Fin t) : Fin ℓ :=
  ⟨(root s).val, by have h := (root s).isLt; have hh := (terminal s).isLt; omega⟩
end ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies
end
section
namespace ConditionedStochasticStabilityHyperbolic.Global.FiltrationPressureConfinement
open LeanShared ShiftedFiltrationGeometry
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ)
def stratum (i : Fin ℓ) : Set X := filtrationLayer (levels T A Λ ℓ N D) i.val
/-- Every literal stratum is measurable. -/
theorem stratum_measurable (hA : IsOpen A) (i : Fin ℓ) :
    MeasurableSet (stratum T A Λ ℓ N D i) := by sorry
end ConditionedStochasticStabilityHyperbolic.Global.FiltrationPressureConfinement
end
section
namespace AbsorbingMarkovChains.FeynmanKac
variable {𝕜 : Type*} [RCLike 𝕜] {M : Type*} [MeasurableSpace M]
/-- Extension by zero at the cemetery. -/
def ext (f : M → 𝕜) : Option M → 𝕜
  | none => 0
  | some y => f y
-- The compared case equations fix the cemetery extension exactly.
omit [MeasurableSpace M] in
theorem ext_none (f : M → 𝕜) : ext f none = 0 := by sorry
omit [MeasurableSpace M] in
theorem ext_some (f : M → 𝕜) (y : M) : ext f (some y) = f y := by sorry
end AbsorbingMarkovChains.FeynmanKac
end
section
namespace ConditionedStochasticStabilityHyperbolic.MeasurableCanonical
open AbsorbingMarkovChains AbsorbingMarkovChains.FeynmanKac Finset
-- Preserve the source declaration context and its exported universe names.
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (C : CanonicalChain X)
/-- The paper's unshifted measurable path average. -/
def pathAverage (h : X → ℝ) (x : X) (n : ℕ) : ℝ :=
  ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ range n, ext h (ω i) ∂C.conditionedMeasure x n
end ConditionedStochasticStabilityHyperbolic.MeasurableCanonical
end
section
namespace ConditionedStochasticStabilityHyperbolic.Global.GlobalAbsorptionEveryControl
variable {X Ω : Type*} [MetricSpace X]
/-- First strictly positive entrance, with infinity when no entrance occurs. -/
def positiveEntranceTime (orbit : ℕ → X) (A : Set X) : WithTop ℕ :=
  ⨅ n : ℕ, ⨅ (_ : 0 < n ∧ orbit n ∈ A), (n : WithTop ℕ)
end ConditionedStochasticStabilityHyperbolic.Global.GlobalAbsorptionEveryControl
end
section
@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.LiteralHG2Clauses
open AbsorbingMarkovChains LeanShared ShiftedFiltrationGeometry
open DerivedHG2Application DerivedHG2Basins
variable {X I Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → CanonicalChain ↥(Aᶜ)) (maps : NNReal → X × Ω → X)
  (ν : Fin t → NNReal → ProbabilityMeasure ↥(Aᶜ))
  (equilibrium : Fin t → ProbabilityMeasure ↥(Aᶜ))
abbrev StableApproach (j : Fin ℓ) (x : X) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index j), dist ((T : X → X)^[n + 1] x) y < r
structure Clauses (δ : NNReal) : Prop where
  number_selected : 0 < t ∧ t ≤ ℓ
  quasiErgodic : ∀ ε, 0 < ε → ε < δ → ∀ s : Fin t, (C ε).IsQuasiErgodic (ν s ε)
  support : ∀ ε, 0 < ε → ε < δ → ∀ s : Fin t,
    {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (originalIndex (root s)))} ⊆ (ν s ε : Measure ↥(Aᶜ)).support
  uniqueness : ∀ ε, 0 < ε → ε < δ → ∀ s : Fin t, ∀ η : Measure ↥(Aᶜ),
    (C ε).IsQuasiErgodic η →
    {x : ↥(Aᶜ) | x.val ∈ Λ (D.index (originalIndex (root s)))} ⊆ η.support →
    η = (ν s ε : Measure ↥(Aᶜ))
  distinct : ∀ ε, 0 < ε → ε < δ → Function.Injective (fun s : Fin t => ν s ε)
  uniform_prefix : ∀ j : Fin ℓ, ∃ s : Fin t,
    ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) 0, StableApproach T A Λ ℓ D j x →
    ∃ hx : x ∈ Aᶜ, ∀ ε, 0 < ε → ε < δ → ∀ f : X → ℝ, Measurable f →
      (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
      Tendsto (MeasurableCanonical.pathAverage (C ε) (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩)
        atTop (𝓝 (∫ y, f y.val ∂(ν s ε : Measure ↥(Aᶜ))))
  all_stable : ∀ j : Fin ℓ, ∃ s : Fin t, ∀ x : X, StableApproach T A Λ ℓ D j x →
    ∃ hx : x ∈ Aᶜ, ∃ δx : NNReal, 0 < δx ∧ ∀ ε, 0 < ε → ε < δx →
    ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
      Tendsto (MeasurableCanonical.pathAverage (C ε) (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩)
        atTop (𝓝 (∫ y, f y.val ∂(ν s ε : Measure ↥(Aᶜ))))
  equilibrium_limit : ∀ s : Fin t, Tendsto (ν s) (𝓝[>] 0) (𝓝 (equilibrium s))
  absorption : ∀ x : X, (∃ n : ℕ, (T : X → X)^[n] x ∈ A) →
    ∃ N : ℕ, 0 < N ∧ ∃ δx : NNReal, 0 < δx ∧ ∀ ε, 0 < ε → ε < δx → ∀ controls : ℕ → Ω,
    GlobalAbsorptionEveryControl.positiveEntranceTime
      (nonautonomousOrbit (fun n z => maps ε (z, controls n)) x) A ≤ (N : WithTop ℕ)
end ConditionedStochasticStabilityHyperbolic.Global.LiteralHG2Clauses
end
end
section
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.LabelledHG2Clauses
open LeanShared ShiftedFiltrationGeometry DerivedHG2Application DerivedHG2Basins
variable {X I : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → AbsorbingMarkovChains.CanonicalChain ↥(Aᶜ))
  (ν : Fin t → NNReal → ProbabilityMeasure ↥(Aᶜ))
structure Clauses (δ : NNReal) : Prop where
  uniform_prefix : ∀ s : Fin t, ∀ i : Fin ((terminal s).val + 1), (root s).val ≤ i.val →
    ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) 0,
      LiteralHG2Clauses.StableApproach T A Λ ℓ D (originalIndex i) x →
      ∃ hx : x ∈ Aᶜ, ∀ ε, 0 < ε → ε < δ → ∀ f : X → ℝ, Measurable f →
        (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
        Tendsto (MeasurableCanonical.pathAverage (C ε) (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩)
          atTop (𝓝 (∫ y, f y.val ∂(ν s ε : Measure ↥(Aᶜ))))
  all_stable : ∀ s : Fin t, ∀ i : Fin ((terminal s).val + 1), (root s).val ≤ i.val →
    ∀ x : X, LiteralHG2Clauses.StableApproach T A Λ ℓ D (originalIndex i) x →
      ∃ hx : x ∈ Aᶜ, ∃ δx : NNReal, 0 < δx ∧ ∀ ε, 0 < ε → ε < δx →
      ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) →
        Tendsto (MeasurableCanonical.pathAverage (C ε) (fun y : ↥(Aᶜ) => f y.val) ⟨x, hx⟩)
          atTop (𝓝 (∫ y, f y.val ∂(ν s ε : Measure ↥(Aᶜ))))
end ConditionedStochasticStabilityHyperbolic.Global.LabelledHG2Clauses
end
end
section
@[expose] public noncomputable section
open Set Function Relation Bundle
open scoped Manifold ContDiff Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Global.PaperHG2GreedySelection
open LeanShared HyperbolicBasicSet Paper
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace M] [BorelSpace M]
  {T : M ≃ₜ M} (D : SpectralDecomposition (E := E) T) (g : M → ℝ) (A : Set M)
attribute [local instance] Classical.propDecidable
abbrev Retained := {i : Fin D.count // D.core i ⊆ Aᶜ}
def edge (i j : Retained D A) : Prop := D.edge i.val j.val
def pressure (i : Retained D A) : ℝ := (D.pressure g i.val).toReal
end ConditionedStochasticStabilityHyperbolic.Global.PaperHG2GreedySelection
end
end
public noncomputable section
open Set Function MeasureTheory Filter IsManifold Bundle
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Palomar
open LeanShared HyperbolicBasicSet Paper Paper.RegularNoise Global
open ShiftedFiltrationGeometry GreedyPrefixGeometry FiltrationPressureConfinement
variable {E ι : Type*} {X : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)] [IsContinuousRiemannianBundle E (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι] {T : X ≃ₜ X}
set_option maxHeartbeats 6400000 in
/-- Theorem 6.5: existentially package the constructed compatible filtration,
its selected prefix roots, the literal killed process, all conditioned-limit
clauses, equilibrium-state limits, and the selected local quasi-ergodic laws.
The geometric and probabilistic meanings of these clauses are stated above;
no auxiliary Anosov system or analytic proof interface is an input. -/
theorem Theorem6_5 [MeasurableSpace E] [BorelSpace E]
    (D0 : SpectralDecomposition (E := E) T) (g φ : X → ℝ) (A : Set X)
    (h : HG2 D0 g A) (strict : MapsTo T (closure A) A)
    (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
    (hw : Continuous (fun x => Real.exp (φ x)))
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, Real.exp (φ x) ≤ R) (hφ : Measurable φ)
    (coreAgreement : ∀ i, D0.core i ⊆ Aᶜ → EqOn (fun x => Real.exp (φ x)) g (D0.core i))
    (localWeightX : ∀ i, D0.core i ⊆ Aᶜ → ∃ W : Set X, IsOpen W ∧ D0.core i ⊆ W ∧
      ∀ ζ : X → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1)
          (ζ * fun x => Real.exp (φ x))) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
    let Λ := fun i : PaperHG2GreedySelection.Retained D0 A => D0.core i.val
    ∃ G : GreedyPrefixGeometry.Data (PaperHG2GreedySelection.edge D0 A)
        (PaperHG2GreedySelection.pressure D0 g A),
    ∃ D : AdaptedSource T A Λ G.order.length,
      D.index = PressureFiltrationSource.reversedVertex G.order ∧
      let j := AssembleShiftedPrefixFamilies.selectedIndex G.order.length G.number G.terminal G.selectedRoot
      ∃ C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain ↥(Aᶜ),
      ∃ ν : Fin G.number → ℝ≥0 → ProbabilityMeasure ↥(Aᶜ),
      ∃ equilibrium : Fin G.number → ProbabilityMeasure ↥(Aᶜ),
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ P.window ∧
        (∀ ε (he : 0 < ε) (window : ε ≤ P.window),
          C ε = RestrictedNoise.chain (L.law ε)
            (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
            (P.raw_measurable ε he window) Aᶜ h.absorbing_open.measurableSet.compl
            (fun x => Real.exp (φ x.val)) (hw.measurable.comp measurable_subtype_coe)
            R hR (fun x => bound x.val)) ∧
        LiteralHG2Clauses.Clauses T A Λ G.order.length D G.number G.terminal G.selectedRoot
          C (ActualOriginalGlobalChain.fixedRawMap P) ν equilibrium δ ∧
        LabelledHG2Clauses.Clauses T A Λ G.order.length D G.number G.terminal G.selectedRoot C ν δ ∧
        (∀ s, ThermodynamicDefinitions.IsEquilibriumState T
          (fun x => φ x - Real.log ((D0.basic (D.index (j s)).val).hyperbolic.unstableJacobian x))
          (Λ (D.index (j s))) ((equilibrium s).map (Subtype.val : ↥(Aᶜ) → X))) ∧
        (∀ s (ζ : ProbabilityMeasure X), ThermodynamicDefinitions.IsEquilibriumState T
          (fun x => φ x - Real.log ((D0.basic (D.index (j s)).val).hyperbolic.unstableJacobian x))
          (Λ (D.index (j s))) ζ → ζ = (equilibrium s).map (Subtype.val : ↥(Aᶜ) → X)) ∧
        (∃ first : Fin G.number, first.val = 0 ∧ ∀ ε, 0 < ε → ε < δ →
          Nonempty (LocalConclusions.SimpleSpectralWitness (C ε) R (ν first ε))) ∧
        ∀ ε (he : 0 < ε) (_small : ε < δ) (window : ε ≤ P.window) (q : Fin G.number),
          let U := stratum T A Λ G.order.length 0 D (j q)
          ∃ νU : ProbabilityMeasure U,
            (νU : Measure U).map Subtype.val = (ν q ε : Measure ↥(Aᶜ)).map Subtype.val ∧
            let CU := RestrictedNoise.chain (L.law ε)
              (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
              (P.raw_measurable ε he window) U
              (stratum_measurable T A Λ G.order.length 0 D h.absorbing_open (j q))
              (fun x => Real.exp (φ x.val)) (hw.measurable.comp measurable_subtype_coe)
              R hR (fun x => bound x.val)
            CU.IsQuasiErgodic (νU : Measure U) ∧
              {x : U | x.val ∈ Λ (D.index (j q))} ⊆ (νU : Measure U).support ∧
              ∀ ζ : Measure U, CU.IsQuasiErgodic ζ →
                {x : U | x.val ∈ Λ (D.index (j q))} ⊆ ζ.support → ζ = (νU : Measure U) := by
  sorry
end ConditionedStochasticStabilityHyperbolic.Palomar
