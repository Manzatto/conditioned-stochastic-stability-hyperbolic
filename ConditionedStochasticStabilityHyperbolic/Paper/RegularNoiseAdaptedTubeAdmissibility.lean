module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedNormalizedTubePartition
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanDecodeRadius
public import LeanShared.Analysis.CylinderPrincipalCoefficient
public import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

/-! Actual normalized tube itineraries yield admissible adapted reference
pseudo-orbits. The common tube radius and noise window are selected before
the horizon, word, labels, or physical starting point. -/
public noncomputable section
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

set_option maxHeartbeats 800000 in
theorem Maps.adapted_normalizedTube_admissibility {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (atlas : ChartAtlas system)
    {η radiusCap : ℝ} (positiveη : 0 < η) (positiveCap : 0 < radiusCap) :
    ∃ radius : ℝ, 0 < radius ∧ radius ≤ radiusCap ∧
      ∃ noiseCap : ℝ≥0, 0 < noiseCap ∧ noiseCap ≤ F.window ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ noiseCap → ∀ N : ℕ,
      ∀ control : Fin N → cube (ι := ι) ε,
      ∀ labels : Fin (N+1) → atlas.NormalizedTubeIndex, ∀ m : M,
      (∀ j : Fin (N+1), CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m ∈
          atlas.normalizedTube radius (labels j)) →
      ∀ k : Fin N, dist (T (labels k.castSucc).val.2.val)
        (labels k.succ).val.2.val < η := by
  let := F.atlas.compactSpace
  have thirdPositive : 0 < η/3 := div_pos positiveη (by norm_num)
  obtain ⟨δ₀,positiveδ₀,uniformT⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous T.continuous) (η/3) thirdPositive
  let δ := min δ₀ (η/3)
  have positiveδ : 0 < δ := lt_min positiveδ₀ thirdPositive
  obtain ⟨decodeRadius,positiveDecode,decode⟩ := atlas.euclidean_decode_radius δ positiveδ
  let radius := min decodeRadius radiusCap
  let noise : ℝ≥0 := ⟨(η/3)/F.constant, (div_pos thirdPositive F.constant_positive).le⟩
  let noiseCap := min noise F.window
  have positiveNoise : 0 < noise := div_pos thirdPositive F.constant_positive
  refine ⟨radius,lt_min positiveDecode positiveCap,min_le_right _ _,
    noiseCap,lt_min positiveNoise F.window_positive,min_le_right _ _,?_⟩
  intro ε positiveε smallε N control labels m tracked k
  have noiseBound : F.constant*(ε:ℝ) ≤ η/3 := by
    rw [mul_comm]
    apply (le_div_iff₀ F.constant_positive).mp
    exact NNReal.coe_le_coe.mpr (smallε.trans (min_le_left _ _))
  have closeAt (j : Fin (N+1)) :
      dist (CylinderPrincipalCoefficient.prefixOrbit
        (fun l : Fin N => F.family ε (control l).val) (fun l => l) j.val m)
        (labels j).val.2.val < δ := by
    let i := labels j
    let a := CylinderPrincipalCoefficient.prefixOrbit
      (fun l : Fin N => F.family ε (control l).val) (fun l => l) j.val m
    have member := tracked j
    change a ∈ (atlas.normalizedTubeChart i).source ∧
      atlas.normalizedTubeChart i a ∈ ball 0 radius at member
    have small : ‖atlas.normalizedTubeChart i a‖ ≤ decodeRadius :=
      (mem_ball_zero_iff.mp member.2).le.trans (min_le_left _ _)
    have actual := (decode i.val.1 i.property.1 i.val.2 i.property.2
      (atlas.normalizedTubeChart i a) small).2
    change dist ((atlas.normalizedTubeChart i).symm (atlas.normalizedTubeChart i a))
      i.val.2.val < δ at actual
    rw [(atlas.normalizedTubeChart i).left_inv member.1] at actual
    exact actual
  let a := CylinderPrincipalCoefficient.prefixOrbit
    (fun l : Fin N => F.family ε (control l).val) (fun l => l) k.val m
  have current : dist a (labels k.castSucc).val.2.val < δ := closeAt k.castSucc
  have nextIdentity : CylinderPrincipalCoefficient.prefixOrbit
      (fun l : Fin N => F.family ε (control l).val) (fun l => l) (k.val+1) m =
        F.family ε (control k).val a := by
    simp only [CylinderPrincipalCoefficient.prefixOrbit,dite_eq_left k.isLt,a]
  have following : dist (F.family ε (control k).val a) (labels k.succ).val.2.val < δ := by
    have item := closeAt k.succ
    rw [show k.succ.val = k.val+1 from rfl,nextIdentity] at item
    exact item
  have images : dist (T (labels k.castSucc).val.2.val) (T a) < η/3 := by
    apply uniformT
    rw [dist_comm]
    exact current.trans_le (min_le_left _ _)
  have noisy : dist (T a) (F.family ε (control k).val a) ≤ η/3 := by
    rw [dist_comm]
    exact (F.uniform_close ε positiveε (smallε.trans (min_le_right _ _)) (control k) a).trans noiseBound
  have finalClose : dist (F.family ε (control k).val a) (labels k.succ).val.2.val < η/3 :=
    following.trans_le (min_le_right _ _)
  have first := dist_triangle (T (labels k.castSucc).val.2.val) (T a) (labels k.succ).val.2.val
  have second := dist_triangle (T a) (F.family ε (control k).val a) (labels k.succ).val.2.val
  linarith

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
