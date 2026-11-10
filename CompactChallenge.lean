module
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
/-!
# Local anisotropic compact embedding (Theorem 3.15)
The supported Schwartz core, all cone-compatible C¹ leaves, graph Gram
measures, Fourier multipliers, and closure norms are specified below.
Definition holes supply graph representations, the resulting core maps and
continuous extensions. Compared identities fix their mathematical action:
heights parametrize the literal leaves; Gram densities fix leaf measures;
Fourier identities fix blocks; AE identities fix the Lp core; coordinate
identities fix reweighting; core agreement fixes the continuous embedding.
-/
@[expose] public noncomputable section
open Set Function MeasureTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap FourierTransform
section
namespace LeanShared.SchwartzJetSpace
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def wordDerivative : List E → 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ)
  | [] => ContinuousLinearMap.id ℂ _
  | v :: w => (LineDeriv.lineDerivOpCLM ℂ 𝓢(E, ℂ) v).comp (wordDerivative w)

end LeanShared.SchwartzJetSpace
end

section
namespace LeanShared.FakeLeafGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def normalized (v : E) : E := ‖v‖⁻¹ • v
/-- The literal signed normalized values in Definition 5.10. -/
def planeErrorValues (P : Submodule ℝ E) (z : E) : Set ℝ :=
  {r | ∃ p ∈ P, p ≠ 0 ∧ r = inner ℝ (normalized z) (normalized p)}

def planeError (P : Submodule ℝ E) (z : E) : ℝ := sSup (planeErrorValues P z)
variable [FiniteDimensional ℝ E]
/-- Cone-contained normal planes of the stipulated stable dimension. -/
def admissiblePlanes (C : Set E) (ds : ℕ) : Set (Submodule ℝ E) :=
  {P | (↑P : Set E) ⊆ C ∧ Module.finrank ℝ P = ds}

def normalErrorValues (C : Set E) (ds : ℕ) (z : E) : Set ℝ :=
  (fun P => planeError P z) '' admissiblePlanes C ds

/-- The literal infimum over admissible planes. -/
def normalError (C : Set E) (ds : ℕ) (z : E) : ℝ := sInf (normalErrorValues C ds z)
def leafErrorValues (C : Set E) (ds : ℕ) (Γ : Set E) : Set ℝ :=
  {r | ∃ x ∈ Γ, ∃ y ∈ Γ, x ≠ y ∧ r = normalError C ds (y - x)}

/-- The literal outer supremum in the fake-leaf condition. -/
def leafError (C : Set E) (ds : ℕ) (Γ : Set E) : ℝ := sSup (leafErrorValues C ds Γ)
end LeanShared.FakeLeafGeometry
end

section
public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An actual embedded C¹ manifold of the specified dimension, carrying the
subspace topology and an injective derivative of its ambient inclusion. -/
def C1Embedded (U : Submodule ℝ E) (Γ : Set E) : Prop :=
  ∃ atlas : ChartedSpace U Γ, letI := atlas
    IsManifold (𝓘(ℝ, U)) 1 Γ ∧
      ContMDiff (𝓘(ℝ, U)) (𝓘(ℝ, E)) 1 (Subtype.val : Γ → E) ∧
      ∀ x : Γ, Function.Injective (mfderiv (𝓘(ℝ, U)) (𝓘(ℝ, E)) (Subtype.val : Γ → E) x)

/-- Every leaf admitted by the paper, with no chosen subfamily. -/
abbrev Index (U : Submodule ℝ E) (C : Set E) :=
  {Γ : Set E // C1Embedded U Γ ∧ FakeLeafGeometry.leafError C (Module.finrank ℝ Uᗮ) Γ = 0}
structure ConeData (U : Submodule ℝ E) (C : Set E) : Prop where
  closed : IsClosed C
  scale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C
  transverse : ∀ v ∈ C, v ∈ U → v = 0
  stable_positive : 0 < Module.finrank ℝ Uᗮ
  normal_planes : (FakeLeafGeometry.admissiblePlanes C (Module.finrank ℝ Uᗮ)).Nonempty
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
end
end

section
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
/-- A positive cone-derived bound for chord slopes of every literal leaf. -/
def slope {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C) : ℝ := by sorry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C)
theorem slope_positive : 0 < slope U C cone := by sorry

theorem slope_bound (Γ : Index U C) : ∀ x ∈ Γ.val, ∀ y ∈ Γ.val,
    ‖Uᗮ.starProjection (x - y)‖ ≤ slope U C cone * ‖U.starProjection (x - y)‖ := by sorry
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
end

section
namespace LeanShared.ConeGraphGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
def graphPoint (U : Submodule ℝ E) (h : U → Uᗮ) (u : U) : E := (u : E) + (h u : E)
end LeanShared.ConeGraphGeometry
end

section
namespace LeanShared.FakeLeafGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (U : Submodule ℝ E) (Γ : Set E)
def projection : Γ → U := fun x => U.orthogonalProjectionOnto (x : E)

def parameterDomain : Set U := range (projection U Γ)
/-- The graph height is zero off the projection image and parametrizes Γ on it. -/
def heightExtension (U : Submodule ℝ E) (Γ : Set E) {L : ℝ} (hL : 0 ≤ L)
    (hslope : ∀ x ∈ Γ, ∀ y ∈ Γ, ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖) :
    U → Uᗮ := by sorry
variable (U : Submodule ℝ E) (Γ : Set E) {L : ℝ} (hL : 0 ≤ L)
  (hslope : ∀ x ∈ Γ, ∀ y ∈ Γ, ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖)
/-- Off-domain values do not introduce a spurious graph. -/
theorem heightExtension_off_domain {u : U} (hu : u ∉ parameterDomain U Γ) :
    heightExtension U Γ hL hslope u = 0 := by sorry
/-- The graph covers exactly the given leaf. -/
theorem graphExtension_image :
    ConeGraphGeometry.graphPoint U (heightExtension U Γ hL hslope) '' parameterDomain U Γ = Γ := by sorry
end LeanShared.FakeLeafGraph
end

section
@[expose] public noncomputable section

open Matrix
open scoped RealInnerProductSpace

namespace LeanShared.GraphJacobian

variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Gram matrix of the derivative `v ↦ (v,Dv)` of a graph. -/
def gram (b : OrthonormalBasis ι ℝ E) (D : E →L[ℝ] F) : Matrix ι ι ℝ :=
  fun i j => (if i = j then 1 else 0) + inner ℝ (D (b i)) (D (b j))

/-- The real density occurring in the classical graph area formula. -/
def density (b : OrthonormalBasis ι ℝ E) (D : E →L[ℝ] F) : ℝ :=
  Real.sqrt (gram b D).det

/-- One bound for all graph derivatives whose norm is at most `L`. -/
def densityBound (L : ℝ) : ℝ :=
  Real.sqrt ((Nat.factorial (Fintype.card ι) : ℝ) * (1 + L ^ 2) ^ Fintype.card ι)
end LeanShared.GraphJacobian
end
end

section
namespace LeanShared.GraphLeafNorm
variable {U E : Type*} [NormedAddCommGroup U] [NormedAddCommGroup E]
  [MeasurableSpace U] [MeasurableSpace E]
/-- Measurable graph data with a common upper bound on its area density.
The parameter-norm bound is supplied by the graph's projection. -/
structure GraphLeaf (U E : Type*) [NormedAddCommGroup U] [NormedAddCommGroup E]
    [MeasurableSpace U] [MeasurableSpace E] (J : ℝ) where
  domain : Set U
  measurable_domain : MeasurableSet domain
  graph : U → E
  measurable_graph : Measurable graph
  injective_graph : Function.Injective graph
  parameter_norm_le : ∀ u, ‖u‖ ≤ ‖graph u‖
  density : U → ℝ≥0∞
  measurable_density : Measurable density
  density_le : ∀ u, density u ≤ ENNReal.ofReal J
namespace GraphLeaf
variable {J : ℝ} (L : GraphLeaf U E J) (μ : Measure U)
/-- The actual weighted parameter measure for this leaf. -/
def sourceMeasure : Measure U := (μ.restrict L.domain).withDensity L.density

/-- The actual ambient graph measure. -/
def measure : Measure E := (L.sourceMeasure μ).map L.graph
end GraphLeaf
end LeanShared.GraphLeafNorm
namespace LeanShared.GraphLeafNorm
variable {A U E : Type*} [NormedAddCommGroup U] [NormedAddCommGroup E]
  [MeasurableSpace U] [MeasurableSpace E] {J : ℝ} (μ : Measure U) (leaves : A → GraphLeaf U E J)
abbrev AmbientFamilySpace := lp (fun a : A => Lp ℂ 1 ((leaves a).measure μ)) ∞
end LeanShared.GraphLeafNorm
end

section
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafDyadicDistribution
open LeanShared AllFakeLeafModel
/-- Graph coordinates for every literal C¹ leaf, specified by the compared description. -/
def family {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]
    (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C) (b : OrthonormalBasis ι ℝ U) :
    Index U C → GraphLeafNorm.GraphLeaf U E (GraphJacobian.densityBound (ι := ι) (slope U C cone)) := by sorry
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafDyadicDistribution
end

section
namespace LeanShared.ConeDyadicSymbols
open scoped ContDiff
/-- The smooth cutoff data stated in the manuscript, with existence left classical. -/
structure RadialCutoff where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  one : ∀ r, |r| ≤ 1 → toFun r = 1
  zero : ∀ r, 2 ≤ |r| → toFun r = 0
  even : ∀ r, toFun (-r) = toFun r
  nonneg : ∀ r, 0 ≤ toFun r
  le_one : ∀ r, toFun r ≤ 1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalized (ξ : E) : E := ‖ξ‖⁻¹ • ξ
/-- A smooth ambient extension of the sphere cutoff. Its existence and cone
separation are the classical angular-cutoff input, not multiplier smoothness. -/
structure AngularCutoff (Cplus Cminus : Set E) where
  toFun : E → ℝ
  smoothAt_unit : ∀ ξ, ‖ξ‖ = 1 → ContDiffAt ℝ ∞ toFun ξ
  nonneg_unit : ∀ ξ, ‖ξ‖ = 1 → 0 ≤ toFun ξ
  le_one_unit : ∀ ξ, ‖ξ‖ = 1 → toFun ξ ≤ 1
  one_on : ∀ ξ ∈ Cplus, ‖ξ‖ = 1 → toFun ξ = 1
  zero_on : ∀ ξ ∈ Cminus, ‖ξ‖ = 1 → toFun ξ = 0

def radial (χ : RadialCutoff) (ξ : E) : ℝ := χ.toFun ‖ξ‖
def annular (χ : RadialCutoff) (ξ : E) : ℝ := radial χ ξ - radial χ ((2 : ℝ) • ξ)
def angle (Φ : E → ℝ) (s : Bool) (ξ : E) : ℝ :=
  if s then Φ (normalized ξ) else 1 - Φ (normalized ξ)
def low (χ : RadialCutoff) : E → ℂ := fun ξ => (radial χ ξ : ℂ) / 2

def highReal (χ : RadialCutoff) (Φ : E → ℝ) (s : Bool) (ξ : E) : ℝ :=
  angle Φ s ξ * annular χ ξ

def high (χ : RadialCutoff) (Φ : E → ℝ) (s : Bool) : E → ℂ :=
  fun ξ => (highReal χ Φ s ξ : ℂ)
/-- The dyadic Schwartz multipliers, fixed pointwise by Palomar.symbols_apply. -/
def symbols [FiniteDimensional ℝ E]
    {Cplus Cminus : Set E} (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) :
    ℕ × Bool → 𝓢(E, ℂ) := by sorry
end LeanShared.ConeDyadicSymbols
end

section
namespace LeanShared.ConeFourierBlocks
/-- Physical Fourier block: its multiplier at Mathlib frequency ξ is σ(2πξ). -/
def block {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (σ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) := by sorry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Fourier action uniquely specifies every block. -/
theorem fourier_block (σ f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (block σ f) ξ = σ ((2 * Real.pi) • ξ) * 𝓕 f ξ := by sorry
end LeanShared.ConeFourierBlocks
end

section
namespace LeanShared.SchwartzJetSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def supportedCore (K : Set E) : Submodule ℂ 𝓢(E, ℂ) where
  carrier := {f | ∀ x ∉ K, f x = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {f g} hf hg := by
    intro x hx
    change f x + g x = 0
    rw [hf x hx, hg x hx, zero_add]
  smul_mem' c f hf := by
    intro x hx
    change c • f x = 0
    rw [hf x hx, smul_zero]
end LeanShared.SchwartzJetSpace
end

section
namespace LeanShared.DyadicCompactness
variable {E F S : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
abbrev BlockSpace := lp (fun _ : ℕ × S => F) ∞
end LeanShared.DyadicCompactness
namespace LeanShared.DyadicCompletion
variable {Core B F S : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup F] [NormedSpace ℂ F]
/-- Completion of the actual block-core range, with its inherited norm. -/
def closedCore (q : Core →ₗ[ℂ] B) : Submodule ℂ B := q.range.topologicalClosure
def coreLift (q : Core →ₗ[ℂ] B) : Core →ₗ[ℂ] closedCore q :=
  q.codRestrict (closedCore q) fun c => q.range.le_topologicalClosure ⟨c, rfl⟩
end LeanShared.DyadicCompletion
namespace LeanShared.DyadicCompletion
variable {Core F S : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
abbrev BlockSpace := DyadicCompactness.BlockSpace (F := F) (S := S)
/-- Coordinate reweighting, specified by Palomar.finalCore_apply. -/
def finalCore (q : Core →ₗ[ℂ] BlockSpace (F := F) (S := S)) (η : ℝ) (hη : 0 < η)
    (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s) : Core →ₗ[ℂ] BlockSpace (F := F) (S := S) := by sorry
end LeanShared.DyadicCompletion
end

section
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafCanonicalDistribution
open LeanShared AllFakeLeafModel AllFakeLeafDyadicDistribution
/-- The supported physical dyadic core in the complete supremum of leaf L¹ spaces. -/
def core {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C) (basis : OrthonormalBasis ι ℝ U)
    {Cp Cm : Set E} (χ : ConeDyadicSymbols.RadialCutoff) (Φ : ConeDyadicSymbols.AngularCutoff Cp Cm)
    {K : Set E} (compact : IsCompact K) (t : Bool → ℝ) :
    SchwartzJetSpace.supportedCore K →ₗ[ℂ]
      DyadicCompletion.BlockSpace (F := GraphLeafNorm.AmbientFamilySpace (volume : Measure U)
        (family U C cone basis)) (S := Bool) := by sorry
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C) (basis : OrthonormalBasis ι ℝ U)
  {Cp Cm : Set E} (χ : ConeDyadicSymbols.RadialCutoff) (Φ : ConeDyadicSymbols.AngularCutoff Cp Cm)
  {K : Set E} (compact : IsCompact K) (t : Bool → ℝ)
abbrev Space := DyadicCompletion.closedCore (core U C cone basis χ Φ compact t)
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafCanonicalDistribution
namespace LeanShared.BTLinkedDyadicWeights
def exponent (t s : ℝ) : Bool → ℝ
  | true => t
  | false => s
end LeanShared.BTLinkedDyadicWeights
end

section
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafCanonicalCrossCone
open LeanShared AllFakeLeafModel AllFakeLeafCanonicalDistribution
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι:Type*} [Fintype ι] [DecidableEq ι]
  (U:Submodule ℝ E) {C D Cm Dm:Set E} (coneC:ConeData U C) (coneD:ConeData U D)
  (basis:OrthonormalBasis ι ℝ U)
  (χ ψ:ConeDyadicSymbols.RadialCutoff)
  (Φ:ConeDyadicSymbols.AngularCutoff C Cm) (Ψ:ConeDyadicSymbols.AngularCutoff D Dm)
  {K:Set E} (compact:IsCompact K) (t s:ℝ)
variable {η:ℝ} (positive:0<η) (δ:Bool→ℝ) (nonnegative:∀b,0≤δ b)
def embedding :
    Space U D coneD basis ψ Ψ compact (BTLinkedDyadicWeights.exponent t s)→L[ℂ]
      DyadicCompletion.closedCore (DyadicCompletion.finalCore
        (core U C coneC basis χ Φ compact (BTLinkedDyadicWeights.exponent t s)) η positive δ nonnegative) := by sorry
theorem embedding_core (inside:C⊆D) (ordered:∀ξ:E,‖ξ‖=1→ξ∉D→ξ∈Cm) (order:s≤t)
    (f:SchwartzJetSpace.supportedCore K) :
    embedding U coneC coneD basis χ ψ Φ Ψ compact t s positive δ nonnegative
      (DyadicCompletion.coreLift (core U D coneD basis ψ Ψ compact (BTLinkedDyadicWeights.exponent t s)) f)=
      DyadicCompletion.coreLift (DyadicCompletion.finalCore
        (core U C coneC basis χ Φ compact (BTLinkedDyadicWeights.exponent t s)) η positive δ nonnegative) f := by sorry
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafCanonicalCrossCone
end
end

section
namespace ConditionedStochasticStabilityHyperbolic
open LeanShared
section CompactEmbedding

open AllFakeLeafModel AllFakeLeafCanonicalDistribution

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 3.15** (`thm:compact_embedding`), in the local form to which the manuscript reduces
it: on a compact `K ⊆ ℝ^d`, for cone systems `Θ = (C, Cm, Φ)` and `Θ' = (D, Dm, Ψ)` with `Θ < Θ'`
(encoded as `C ⊆ D` and every unit vector outside `D` lying in `Cm`) and `s ≤ t`, the anisotropic
space `B^{Θ',t,s}(K)` built from all `C¹` fake unstable leaves embeds compactly and injectively in
`B^{Θ,t',s'}(K)` with `t' = t - η - δ true` and `s' = s - η - δ false`, for every `η > 0` and
`δ ≥ 0`. -/
theorem Theorem3_15 (U : Submodule ℝ E) {C D Cm Dm : Set E}
    (coneC : ConeData U C) (coneD : ConeData U D) (basis : OrthonormalBasis ι ℝ U)
    (χ ψ : ConeDyadicSymbols.RadialCutoff)
    (Φ : ConeDyadicSymbols.AngularCutoff C Cm) (Ψ : ConeDyadicSymbols.AngularCutoff D Dm)
    {K : Set E} (compact : IsCompact K) (t s : ℝ) {η : ℝ} (positive : 0 < η) (δ : Bool → ℝ)
    (nonnegative : ∀ b, 0 ≤ δ b) (inside : C ⊆ D)
    (ordered : ∀ ξ : E, ‖ξ‖ = 1 → ξ ∉ D → ξ ∈ Cm) (order : s ≤ t) :
    IsCompactOperator (AllFakeLeafCanonicalCrossCone.embedding U coneC coneD basis χ ψ Φ Ψ compact
        t s positive δ nonnegative) ∧
      Injective (AllFakeLeafCanonicalCrossCone.embedding U coneC coneD basis χ ψ Φ Ψ compact
        t s positive δ nonnegative) := by sorry
end CompactEmbedding
end ConditionedStochasticStabilityHyperbolic
end
public noncomputable section
open Set Function MeasureTheory
open scoped SchwartzMap FourierTransform Topology ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Palomar
open LeanShared AllFakeLeafModel AllFakeLeafDyadicDistribution
section Leaves
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]
  (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C) (basis : OrthonormalBasis ι ℝ U)
/-- Leaf domains, graphs, and densities are the actual orthogonal graph data. -/
theorem family_description (Γ : Index U C) :
    let h := FakeLeafGraph.heightExtension U Γ.val (slope_positive U C cone).le (slope_bound U C cone Γ)
    (family U C cone basis Γ).domain = FakeLeafGraph.parameterDomain U Γ.val ∧
    (family U C cone basis Γ).graph = ConeGraphGeometry.graphPoint U h ∧
    (family U C cone basis Γ).density = (FakeLeafGraph.parameterDomain U Γ.val).indicator
      (fun u => ENNReal.ofReal (GraphJacobian.density basis (fderiv ℝ h u))) := by
  sorry
/-- Projection domains are open, so the displayed derivatives are local graph derivatives. -/
theorem family_domain_open (Γ : Index U C) : IsOpen (family U C cone basis Γ).domain := by
  sorry
end Leaves
section Symbols
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise low-frequency and rescaled high-frequency cone symbols. -/
theorem symbols_apply {Cp Cm : Set E} (χ : ConeDyadicSymbols.RadialCutoff)
    (Φ : ConeDyadicSymbols.AngularCutoff Cp Cm) (j : ℕ × Bool) (ξ : E) :
    ConeDyadicSymbols.symbols χ Φ j ξ =
      if j.1 = 0 then ConeDyadicSymbols.low χ ξ else
        ConeDyadicSymbols.high χ Φ.toFun j.2 (((2 : ℝ) ^ j.1)⁻¹ • ξ) := by
  sorry
end Symbols
section Core
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C) (basis : OrthonormalBasis ι ℝ U)
  {Cp Cm : Set E} (χ : ConeDyadicSymbols.RadialCutoff) (Φ : ConeDyadicSymbols.AngularCutoff Cp Cm)
  {K : Set E} (compact : IsCompact K) (t : Bool → ℝ)
/-- Each Lp coordinate is exactly the weighted physical Fourier block on its leaf. -/
theorem core_ae (f : SchwartzJetSpace.supportedCore K) (j : ℕ × Bool) (Γ : Index U C) :
    AllFakeLeafCanonicalDistribution.core U C cone basis χ Φ compact t f j Γ
      =ᵐ[(family U C cone basis Γ).measure (volume : Measure U)]
      fun x => (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) * ConeFourierBlocks.block
        (ConeDyadicSymbols.symbols χ Φ j) f.val x := by
  sorry
/-- The completed space has exactly the closure of the physical block-core range. -/
theorem space_mem_iff
    (b : DyadicCompletion.BlockSpace
      (F := GraphLeafNorm.AmbientFamilySpace (volume : Measure U) (family U C cone basis))
      (S := Bool)) :
    b ∈ AllFakeLeafCanonicalDistribution.Space U C cone basis χ Φ compact t ↔
      b ∈ closure (Set.range (AllFakeLeafCanonicalDistribution.core U C cone basis χ Φ compact t)) := by
  sorry
end Core
section Reweight
variable {Core F S : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
/-- The target completion has precisely the stated independent exponent losses. -/
theorem finalCore_apply (q : Core →ₗ[ℂ] DyadicCompletion.BlockSpace (F := F) (S := S))
    (η : ℝ) (hη : 0 < η) (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s) (f : Core) (j : ℕ × S) :
    DyadicCompletion.finalCore q η hη δ hδ f j =
      (((2 : ℝ) ^ (-δ j.2 * j.1) : ℝ) : ℂ) •
        (((((2 : ℝ) ^ (-η)) ^ j.1) : ℝ) : ℂ) • q f j := by
  sorry
end Reweight
end ConditionedStochasticStabilityHyperbolic.Palomar
