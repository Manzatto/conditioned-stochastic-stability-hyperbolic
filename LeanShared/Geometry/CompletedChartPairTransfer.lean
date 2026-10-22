module

public import LeanShared.Geometry.RegularChartPairTransfer
public import LeanShared.Analysis.DyadicCompletion
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Constructed ordinary chart coordinates and global regular realization

Only smooth-core ordinary C^u coordinate bounds and local anisotropic
bounds are inputs. Dense extension constructs ordinary local coordinates
and the local anisotropic realizations. Continuous point evaluation proves
that these represent the literal cutoff chart functions on every regular
input. Density then constructs their global realized value in exactly the
closure of the genuine maximum chart core.

This supplies the completed coordinate and operator-core identities used by
finite chart microlocal aggregation, rather than assuming them.
-/

@[expose] public noncomputable section

open Set IsManifold
open scoped Manifold ContDiff SchwartzMap BigOperators

namespace LeanShared.CompletedChartPairTransfer

open DyadicCompletion

variable {E M AtlasIndex Core Reg : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  (e : AtlasIndex → OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)
  (he : ∀ j, e j ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  (functions : Core →ₗ[ℂ] (M → ℂ))
  (smooth : ∀ f : Core, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (functions f))
  (view : Reg →ₗ[ℂ] (M → ℂ))
  (regularCore : Core →ₗ[ℂ] Reg) (dense : DenseRange regularCore)
  (viewCore : ∀ c, view (regularCore c) = functions c)
  (evaluate : M → Reg →L[ℂ] ℂ) (evaluation : ∀ x f, evaluate x f = view f x)
  {LocalReg : D.indices → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  (localView : ∀ i, LocalReg i →ₗ[ℂ] (E → ℂ)) (localInj : ∀ i, Function.Injective (localView i))
  (localCore : ∀ i, SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D i) →ₗ[ℂ] LocalReg i)
  (localDense : ∀ i, DenseRange (localCore i))
  (localViewCore : ∀ i f, localView i (localCore i f) = f.val)
  (localEvaluate : ∀ i, E → LocalReg i →L[ℂ] ℂ)
  (localEvaluation : ∀ i x f, localEvaluate i x f = localView i f x)
  (Ccoord : D.indices → ℝ)
  (coordinateBound : ∀ i c,
    ‖localCore i (ConstructedManifoldLocalization.localize e D he functions smooth i c)‖ ≤ Ccoord i * ‖regularCore c‖)

/-- The local ordinary C^u coordinate map is constructed on the dense
smooth core; no full regular-space coordinate map is assumed. -/
def coordinate (i : D.indices) : Reg →L[ℂ] LocalReg i :=
  ((localCore i).comp (ConstructedManifoldLocalization.localize e D he functions smooth i)).extendOfNorm regularCore

include dense coordinateBound in
theorem coordinate_core (i : D.indices) (c : Core) :
    coordinate e D he functions smooth regularCore localCore i (regularCore c) =
      localCore i (ConstructedManifoldLocalization.localize e D he functions smooth i c) :=
  LinearMap.extendOfNorm_eq (f := (localCore i).comp
    (ConstructedManifoldLocalization.localize e D he functions smooth i))
    (e := regularCore) dense ⟨Ccoord i, coordinateBound i⟩ c

include dense viewCore evaluation localViewCore localEvaluation coordinateBound in
/-- Every constructed ordinary coordinate represents the actual cutoff
function, with no assertion of smooth output. -/
theorem coordinate_view (i : D.indices) (r : Reg) (y : E) :
    localView i (coordinate e D he functions smooth regularCore localCore i r) y =
      ChartLocalization.coordinate (e i) (D.cutoff i) (view r) y := by
  classical
  have hleft : Continuous (fun r => localEvaluate i y (coordinate e D he functions smooth regularCore localCore i r)) :=
    (localEvaluate i y).continuous.comp (coordinate e D he functions smooth regularCore localCore i).continuous
  have hright : Continuous (fun r => ChartLocalization.coordinate (e i) (D.cutoff i) (view r) y) := by
    by_cases hy : y ∈ (e i).target
    · simp only [ChartLocalization.coordinate, ite_eq_left hy]
      exact continuous_const.mul (((evaluate ((e i).symm y)).continuous).congr (evaluation _))
    · simp only [ChartLocalization.coordinate, ite_eq_right hy]
      exact continuous_const
  have hl : Continuous (fun r => localView i (coordinate e D he functions smooth regularCore localCore i r) y) :=
    hleft.congr (fun r => localEvaluation i y _)
  refine dense.induction_on (p := fun r =>
    localView i (coordinate e D he functions smooth regularCore localCore i r) y =
      ChartLocalization.coordinate (e i) (D.cutoff i) (view r) y) r (isClosed_eq hl hright) ?_
  intro c
  rw [coordinate_core e D he functions smooth regularCore dense localCore Ccoord coordinateBound,
    localViewCore, viewCore]
  rfl

variable {B : D.indices → Type*} [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℂ (B i)]
  [∀ i, CompleteSpace (B i)]
  (sourceBlock : ∀ i, SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D i) →ₗ[ℂ] B i)
  (Cblock : D.indices → ℝ)
  (blockBound : ∀ i f, ‖sourceBlock i f‖ ≤ Cblock i * ‖localCore i f‖)

/-- Classical local anisotropic/Hölder bounds construct each local
realization, using the actual physical source blocks. -/
def localRealize (i : D.indices) : LocalReg i →L[ℂ] B i :=
  (sourceBlock i).extendOfNorm (localCore i)

include localDense blockBound in
omit [∀ i, CompleteSpace (LocalReg i)] in
theorem localRealize_core (i : D.indices) (f : SchwartzJetSpace.supportedCore
    (ConstructedManifoldLocalization.support e D i)) :
    localRealize e D localCore sourceBlock i (localCore i f) = sourceBlock i f :=
  LinearMap.extendOfNorm_eq (f := sourceBlock i) (e := localCore i)
    (localDense i) ⟨Cblock i, blockBound i⟩ f

/-- The genuine smooth maximum-chart core used by the manifold spaces. -/
def coreMap : Core →ₗ[ℂ] (∀ i, B i) := LinearMap.pi fun i =>
  (sourceBlock i).comp (ConstructedManifoldLocalization.localize e D he functions smooth i)

def chartValues : Reg →L[ℂ] (∀ i, B i) := ContinuousLinearMap.pi fun i =>
  (localRealize e D localCore sourceBlock i).comp (coordinate e D he functions smooth regularCore localCore i)

include dense localDense coordinateBound blockBound in
theorem chartValues_core (c : Core) :
    chartValues e D he functions smooth regularCore localCore sourceBlock (regularCore c) =
      coreMap e D he functions smooth sourceBlock c := by
  funext i
  change localRealize e D localCore sourceBlock i
    (coordinate e D he functions smooth regularCore localCore i (regularCore c)) = _
  rw [coordinate_core e D he functions smooth regularCore dense localCore Ccoord coordinateBound,
    localRealize_core e D localCore localDense sourceBlock Cblock blockBound]
  rfl

include dense localDense coordinateBound blockBound in
theorem chartValues_mem (r : Reg) :
    chartValues e D he functions smooth regularCore localCore sourceBlock r ∈
      closedCore (coreMap e D he functions smooth sourceBlock) := by
  have hc : IsClosed {r : Reg | chartValues e D he functions smooth regularCore localCore sourceBlock r ∈
      closedCore (coreMap e D he functions smooth sourceBlock)} := by
    change IsClosed ((chartValues e D he functions smooth regularCore localCore sourceBlock) ⁻¹'
      closure (Set.range (coreMap e D he functions smooth sourceBlock)))
    exact isClosed_closure.preimage (chartValues e D he functions smooth regularCore localCore sourceBlock).continuous
  refine dense.induction_on r hc ?_
  intro c
  rw [chartValues_core e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound]
  exact subset_closure ⟨c, rfl⟩

/-- The global regular realization is constructed in the literal completed
chart norm, with its actual coordinates and common core. -/
def realization : Reg →L[ℂ] closedCore (coreMap e D he functions smooth sourceBlock) :=
  (chartValues e D he functions smooth regularCore localCore sourceBlock).codRestrict
    (closedCore (coreMap e D he functions smooth sourceBlock))
    (chartValues_mem e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound
      sourceBlock Cblock blockBound)

include dense localDense coordinateBound blockBound in
theorem realization_core (c : Core) :
    realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound
      (regularCore c) = coreLift (coreMap e D he functions smooth sourceBlock) c := by
  apply Subtype.ext
  exact chartValues_core e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound c

include dense viewCore evaluation localViewCore localEvaluation coordinateBound in
/-- The literal coordinate lies in the local finite-Hölder range because
its representing element has been constructed by dense extension. -/
theorem coordinate_member (i : D.indices) (r : Reg) :
    RegularChartPairTransfer.coordinate (e i) (D.cutoff i) (view r) ∈ (localView i).range := by
  refine ⟨coordinate e D he functions smooth regularCore localCore i r, ?_⟩
  funext y
  exact coordinate_view e D he functions smooth view regularCore dense viewCore evaluate evaluation
    localView localCore localViewCore localEvaluate localEvaluation Ccoord coordinateBound i r y

include dense viewCore evaluation localViewCore localEvaluation coordinateBound in
/-- Faithfulness identifies the lifted literal coordinate with the new bounded ordinary coordinate
constructed on the common core. -/
theorem lifted_coordinate_eq (i : D.indices) (r : Reg) :
    RegularChartPairTransfer.localCoordinate e D view localView localInj
      (coordinate_member e D he functions smooth view regularCore dense viewCore evaluate evaluation
        localView localCore localViewCore localEvaluate localEvaluation Ccoord coordinateBound) i r =
      coordinate e D he functions smooth regularCore localCore i r := by
  apply localInj i
  exact (RegularChartPairTransfer.lift_view (localView i) (localInj i)
    ((RegularChartPairTransfer.coordinate (e i) (D.cutoff i)).comp view)
    (coordinate_member e D he functions smooth view regularCore dense viewCore evaluate evaluation
      localView localCore localViewCore localEvaluate localEvaluation Ccoord coordinateBound i) r).trans
    (funext fun y => (coordinate_view e D he functions smooth view regularCore dense viewCore evaluate evaluation
      localView localCore localViewCore localEvaluate localEvaluation Ccoord coordinateBound i r y).symm)

variable (inj : Function.Injective view) (F : M → M) (g : M → ℝ)
  (regular : ∀ c, FiniteRegularTransferRealization.weightedComposition F g (functions c) ∈ view.range)

include dense viewCore evaluation localViewCore localEvaluation coordinateBound localDense blockBound in
/-- The finite-chart row-vector used in microscopic aggregation is exactly
the normed coordinate vector of the same constructed global realization. -/
theorem realization_action_norm (c : Core) :
    ‖realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound
      (RegularChartPairTransfer.globalAction functions view inj F g regular c)‖ =
    ‖RegularChartPairTransfer.outputCore e D functions view inj F g regular localView localInj
      (coordinate_member e D he functions smooth view regularCore dense viewCore evaluate evaluation
        localView localCore localViewCore localEvaluate localEvaluation Ccoord coordinateBound)
      (fun i => (localRealize e D localCore sourceBlock i).toLinearMap) c‖ := by
  have heq :
      (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound
        (RegularChartPairTransfer.globalAction functions view inj F g regular c) : ∀ i, B i) =
      RegularChartPairTransfer.outputCore e D functions view inj F g regular localView localInj
        (coordinate_member e D he functions smooth view regularCore dense viewCore evaluate evaluation
          localView localCore localViewCore localEvaluate localEvaluation Ccoord coordinateBound)
        (fun i => (localRealize e D localCore sourceBlock i).toLinearMap) c := by
    funext i
    exact congrArg (localRealize e D localCore sourceBlock i)
      (lifted_coordinate_eq e D he functions smooth view regularCore dense viewCore evaluate evaluation
        localView localInj localCore localViewCore localEvaluate localEvaluation Ccoord coordinateBound i
        (RegularChartPairTransfer.globalAction functions view inj F g regular c)).symm
  exact congrArg norm heq

end LeanShared.CompletedChartPairTransfer
