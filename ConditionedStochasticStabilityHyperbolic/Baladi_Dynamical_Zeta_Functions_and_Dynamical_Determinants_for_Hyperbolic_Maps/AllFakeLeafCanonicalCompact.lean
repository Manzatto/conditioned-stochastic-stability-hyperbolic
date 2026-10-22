module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafCanonicalCrossCone
public import LeanShared.Analysis.ConstructedSchwartzCutoff

/-! Compact injection of the literal all-fake-leaf anisotropic completions
for ordered cones and independent positive losses in both exponents.
Smooth-core boundedness, comparison, distribution order and faithfulness
are proved producers, rather than assumptions of this theorem. -/
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
  {η:ℝ} (positive:0<η) (δ:Bool→ℝ) (nonnegative:∀b,0≤δ b)

private theorem compact_impl : IsCompactOperator
    (embedding U coneC coneD basis χ ψ Φ Ψ compact t s positive δ nonnegative) := by
  let r := max 0 compact.isBounded.exists_norm_le.choose
  have nonnegativeR : 0≤r := le_max_left _ _
  have radius (x:E) (hx:x∈K) : ‖x‖≤r :=
    (compact.isBounded.exists_norm_le.choose_spec x hx).trans (le_max_right _ _)
  let L := Metric.closedBall (0:E) (r+2)
  let cutoff := ConstructedSchwartzCutoff.cutoff r nonnegativeR (E:=E)
  let e := BTLinkedDyadicWeights.exponent t s
  let n := AllFakeLeafDyadicDistribution.growth e+1
  let words := LaplacianFiniteJet.testWords (stdOrthonormalBasis ℝ E) n
  let coefficient := AllFakeLeafDyadicDistribution.constant U C coneC basis χ Φ e*
    ((1+(r+2))^(AllFakeLeafDistribution.order U)*
      (Fintype.card (LaplacianFiniteJet.Index (Fin (Module.finrank ℝ E)) 0)+
        Fintype.card (LaplacianFiniteJet.Index (Fin (Module.finrank ℝ E)) n)))
  apply CrossConeCompactEmbedding.embedding_isCompact volume
    (AllFakeLeafDyadicDistribution.slopeBound U C coneC basis)
    (AllFakeLeafDyadicDistribution.family U C coneC basis) K χ Φ e
    (bounded U C coneC basis χ Φ compact e)
    (core U D coneD basis ψ Ψ compact e) positive δ nonnegative words
    (show IsCompact L from isCompact_closedBall _ _) cutoff
    (fun x hx=>ConstructedSchwartzCutoff.supported r nonnegativeR x hx)
    (fun x hx=>ConstructedSchwartzCutoff.one r nonnegativeR (radius x hx))
    (pair U C coneC basis χ Φ compact e) coefficient
  · exact mul_nonneg (AllFakeLeafDyadicDistribution.constant_nonnegative U C coneC basis χ Φ e) (by positivity)
  · intro z test supported
    exact AllFakeLeafDyadicDistribution.finite_order_bound U C coneC basis χ Φ K e
      (bounded U C coneC basis χ Φ compact e) (stdOrthonormalBasis ℝ E) L
      Metric.isClosed_closedBall (r+2) (by linarith)
      (fun x hx=>by simpa only [L,Metric.mem_closedBall,dist_zero_right] using hx) z test supported
  · intro f test
    exact AllFakeLeafDyadicDistribution.pairing_core U C coneC basis χ Φ K e
      (bounded U C coneC basis χ Φ compact e) f test

theorem compact_injective_embedding (inside:C⊆D)
    (ordered:∀ξ:E,‖ξ‖=1→ξ∉D→ξ∈Cm) (order:s≤t) :
    IsCompactOperator (embedding U coneC coneD basis χ ψ Φ Ψ compact t s positive δ nonnegative) ∧
      Function.Injective (embedding U coneC coneD basis χ ψ Φ Ψ compact t s positive δ nonnegative) :=
  ⟨compact_impl U coneC coneD basis χ ψ Φ Ψ compact t s positive δ nonnegative,
    embedding_injective U coneC coneD basis χ ψ Φ Ψ compact t s positive δ nonnegative inside ordered order⟩
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafCanonicalCrossCone
