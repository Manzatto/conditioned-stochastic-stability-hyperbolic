module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderPhysicalModel
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderPhysicalModel

/-! Construction of the physical model from its genuine chart geometry.
Local regular spaces, dense cores, coordinate bounds, smooth block
boundedness and local anisotropic norm bounds are all produced internally. -/
public noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedHolderCompactModel
open ConstructedHolderPhysicalModel
open LeanShared
variable {E U M J A Ω:Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  {V S:Set M} (e:J→OpenPartialHomeomorph M E)
  (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀j,e j∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (openV:IsOpen V) (region:V⊆S) {b:ℝ} (hb:0<b) (hb1:b<1)


omit [MeasurableSpace E] [BorelSpace E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem identity_invariant : ∀(_a:Ω) (f:Regular e D openV hb hb1),
    FiniteRegularTransferRealization.weightedComposition (fun x:M=>x) (fun _=>1)
      (view e D openV hb hb1 f)∈(view e D openV hb hb1).range := by
  intro a f
  refine ⟨f,?_⟩
  ext x
  change _=(1:ℂ)*_
  exact (one_mul _).symm

omit [MeasurableSpace E] [BorelSpace E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem identity_bound (a:Ω) (f:Regular e D openV hb hb1) :
    ‖InvariantFiniteRegularTransfer.action (view e D openV hb hb1)
      (view_injective e D openV hb hb1) (fun (_:Ω) (x:M)=>x) (fun _=>1)
      (identity_invariant e D openV hb hb1) a f‖≤1*‖f‖ := by
  have eqn : InvariantFiniteRegularTransfer.action (view e D openV hb hb1)
      (view_injective e D openV hb hb1) (fun (_:Ω) (x:M)=>x) (fun _=>1)
      (identity_invariant e D openV hb hb1) a f=f := by
    apply view_injective e D openV hb hb1
    ext x
    exact (InvariantFiniteRegularTransfer.action_apply _ _ _ _ _ a f x).trans (one_mul _)
  rw [eqn,one_mul]

variable (μ:Measure U) [μ.IsAddHaarMeasure] {slope:ℝ} (hSlope:0≤slope)
  (leaves:D.indices→A→GraphLeafNorm.GraphLeaf U E slope)
  (plus minus:D.indices→Set E) (radial:D.indices→ConeDyadicSymbols.RadialCutoff)
  (angle:∀i,ConeDyadicSymbols.AngularCutoff (plus i) (minus i))
  (exponent:D.indices→Bool→ℝ) (margin:∀i a,exponent i a≤b)
  (lossH lossW:D.indices→ℝ) (hH:∀i,0<lossH i) (hW:∀i,0<lossW i)
  (extraH extraW:D.indices→Bool→ℝ) (hEH:∀i a,0≤extraH i a) (hEW:∀i a,0≤extraW i a)

/-- Physical spaces require no transfer calculus assumptions. The identity
and unit weight fill metadata; all Fourier/chart norms are the original
literal ones, independently of this metadata. -/
@[expose] def model := ConstructedHolderPhysicalModel.model (Ω:=Ω)
  e D atlas openV region hb hb1 μ hSlope leaves plus minus radial angle exponent margin
  lossH lossW hH hW extraH extraW hEH hEW
  (fun (_:Ω) (x:M)=>x) (fun _=>1) (identity_invariant e D openV hb hb1)
  1 (identity_bound e D openV hb hb1)

end ConditionedStochasticStabilityHyperbolic.ConstructedHolderCompactModel
