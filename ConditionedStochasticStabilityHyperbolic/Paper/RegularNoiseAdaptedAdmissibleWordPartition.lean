module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeAdmissibility
public import LeanShared.Geometry.FiniteCaptureWordCutoffs

/-! An actual finite smooth tube partition yields literal finite-word
cutoffs. Every nonzero cutoff is an admissible adapted reference itinerary;
inadmissible cutoffs vanish, so deleting them preserves exact partition
unity without a multiplicity factor. -/
@[expose] public noncomputable section
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

def adaptedTubeWordAdmissible (atlas : ChartAtlas system) (η : ℝ)
    (s : Finset atlas.NormalizedTubeIndex) {N : ℕ} (labels : Fin (N+1) → s) : Prop :=
  ∀ k : Fin N, dist (T (labels k.castSucc).val.val.2.val)
    (labels k.succ).val.val.2.val < η

set_option maxHeartbeats 800000 in
theorem Maps.exists_adapted_admissibleWord_partition {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (atlas : ChartAtlas system)
    {η radiusCap : ℝ} (positiveη : 0 < η) (positiveCap : 0 < radiusCap) :
    ∃ radius : ℝ, 0 < radius ∧ radius ≤ radiusCap ∧
      ∃ noiseCap : ℝ≥0, 0 < noiseCap ∧ noiseCap ≤ F.window ∧
      ∃ s : Finset atlas.NormalizedTubeIndex,
      ∃ d : FiniteSmoothCapturePartition.Data (E := E) Λ
        (fun i : s => atlas.normalizedTube radius i.val), Λ ⊆ d.capture ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ noiseCap → ∀ N : ℕ,
      ∀ control : Fin N → cube (ι := ι) ε,
      let points := fun (m : M) (j : Fin (N+1)) => CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m
      (∀ (labels : Fin (N+1) → s) (m : M),
        FiniteSmoothCapturePartition.wordCutoff d (points m) labels ≠ 0 →
          (∀ j : Fin (N+1), points m j ∈
            (atlas.normalizedTubeChart (labels j).val).source ∧
            atlas.normalizedTubeChart (labels j).val (points m j) ∈ ball 0 radius) ∧
          adaptedTubeWordAdmissible atlas η s labels) ∧
      (∀ labels : Fin (N+1) → s, ¬ adaptedTubeWordAdmissible atlas η s labels →
        ∀ m : M, FiniteSmoothCapturePartition.wordCutoff d (points m) labels = 0) ∧
      (∀ m : M, (∀ j : Fin (N+1), points m j ∈ d.capture) →
        ∑ labels ∈ (Finset.univ : Finset (Fin (N+1) → s)).filter
          (adaptedTubeWordAdmissible atlas η s),
          FiniteSmoothCapturePartition.wordCutoff d (points m) labels = 1) := by
  obtain ⟨radius,positiveRadius,belowRadius,noiseCap,positiveNoise,belowNoise,admissibility⟩ :=
    F.adapted_normalizedTube_admissibility atlas positiveη positiveCap
  obtain ⟨s,d,coreCapture⟩ := F.exists_adapted_normalizedTube_partition atlas positiveRadius
  refine ⟨radius,positiveRadius,belowRadius,noiseCap,positiveNoise,belowNoise,s,d,coreCapture,?_⟩
  intro ε positiveε smallε N control
  dsimp only
  let points := fun (m : M) (j : Fin (N+1)) => CylinderPrincipalCoefficient.prefixOrbit
    (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m
  have tracked (labels : Fin (N+1) → s) (m : M)
      (nonzero : FiniteSmoothCapturePartition.wordCutoff d (points m) labels ≠ 0)
      (j : Fin (N+1)) : points m j ∈ atlas.normalizedTube radius (labels j).val :=
    FiniteSmoothCapturePartition.wordCutoff_nonzero_mem d (points m) labels nonzero j
  have admissible (labels : Fin (N+1) → s) (m : M)
      (nonzero : FiniteSmoothCapturePartition.wordCutoff d (points m) labels ≠ 0) :
      adaptedTubeWordAdmissible atlas η s labels :=
    admissibility ε positiveε smallε N control (fun j => (labels j).val) m (tracked labels m nonzero)
  have vanishes (labels : Fin (N+1) → s)
      (invalid : ¬ adaptedTubeWordAdmissible atlas η s labels) (m : M) :
      FiniteSmoothCapturePartition.wordCutoff d (points m) labels = 0 := by
    by_contra nonzero
    exact invalid (admissible labels m nonzero)
  refine ⟨?_,vanishes,?_⟩
  · intro labels m nonzero
    exact ⟨tracked labels m nonzero,admissible labels m nonzero⟩
  · intro m capture
    calc
      _ = ∑ labels : Fin (N+1) → s,
          FiniteSmoothCapturePartition.wordCutoff d (points m) labels := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro labels _ excluded
        exact vanishes labels (by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using excluded) m
      _ = 1 := by
        convert FiniteSmoothCapturePartition.wordCutoff_sum d (points m) capture using 1
        congr 1
        ext labels
        simp only [Finset.mem_univ]

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
