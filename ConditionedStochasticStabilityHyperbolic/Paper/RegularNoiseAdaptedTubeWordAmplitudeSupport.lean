module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedAdmissibleWordPartition
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedExtensionWordAgreement
public import LeanShared.Geometry.ChartLocalization

/-! Literal beta-weighted source amplitudes have the actual physical
cylinder witnesses and both endpoint bounds required by the principal row.
Finite labels are extended constantly after the horizon, preserving all
selected adapted charts and reference points. -/
@[expose] public noncomputable section
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff NNReal Topology BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.CenteredManifoldCoordinates
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

namespace AdaptedTubeWord
variable (atlas : ChartAtlas system) (s : Finset atlas.NormalizedTubeIndex)
  {N : ℕ} (labels : Fin (N+1) → s)

def indexAt (k : ℕ) : atlas.NormalizedTubeIndex :=
  (labels ⟨min k N,Nat.lt_succ_of_le (min_le_right k N)⟩).val

def center (k : ℕ) : Λ := (indexAt atlas s labels k).val.1

def reference (k : ℕ) : Λ := (indexAt atlas s labels k).val.2

theorem center_mem (k : ℕ) : center atlas s labels k ∈ atlas.centers :=
  (indexAt atlas s labels k).property.1

theorem reference_mem (k : ℕ) : reference atlas s labels k ∈
    atlas.patch (center atlas s labels k) := (indexAt atlas s labels k).property.2

def chart (k : ℕ) : OpenPartialHomeomorph M system.EuclideanModel :=
  atlas.normalizedTubeChart (indexAt atlas s labels k)

theorem chart_eq (j : Fin (N+1)) :
    chart atlas s labels j.val = atlas.normalizedTubeChart (labels j).val := by
  simp only [chart,indexAt,min_eq_left (Nat.le_of_lt_succ j.isLt)]

theorem reference_admissible {η : ℝ}
    (admissible : adaptedTubeWordAdmissible atlas η s labels) :
    ∀ k < N, dist (T (reference atlas s labels k).val)
      (reference atlas s labels (k+1)).val < η := by
  intro k hk
  have item := admissible ⟨k,hk⟩
  change dist (T (labels ⟨k,Nat.lt_succ_of_le (Nat.le_of_lt hk)⟩).val.val.2.val)
    (labels ⟨k+1,Nat.lt_succ_of_le (Nat.succ_le_of_lt hk)⟩).val.val.2.val < η at item
  simpa only [reference,indexAt,min_eq_left (Nat.le_of_lt hk),
    min_eq_left (Nat.succ_le_of_lt hk)] using item

end AdaptedTubeWord

set_option maxHeartbeats 800000 in
theorem Maps.adapted_tubeWord_amplitude_support {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (atlas : ChartAtlas system)
    {radius agreementRadius rowRadius : ℝ}
    (smallAgreement : radius ≤ agreementRadius) (smallRow : radius ≤ rowRadius)
    (s : Finset atlas.NormalizedTubeIndex)
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : s => atlas.normalizedTube radius i.val))
    (ε : ℝ≥0) {N : ℕ} (control : Fin N → cube (ι := ι) ε)
    (labels : Fin (N+1) → s) (amplitude : M → ℂ) :
    let c := AdaptedTubeWord.center atlas s labels
    let p := AdaptedTubeWord.reference atlas s labels
    let inside := AdaptedTubeWord.reference_mem atlas s labels
    let κ := AdaptedTubeWord.chart atlas s labels
    let cutoff := fun m => (FiniteSmoothCapturePartition.wordCutoff d
      (fun j : Fin (N+1) => CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m) labels : ℂ)
    let g := ChartLocalization.coordinate (κ 0) cutoff amplitude
    ∀ H : Fin N → system.EuclideanModel ≃ₜ system.EuclideanModel,
    (∀ k : Fin N,
      let L := ContinuousCenteredFrameCharts.chartFrame (c k.val).val (p k.val).val
        (atlas.inside (c k.val) (inside k.val)).2
        (system.euclideanReferenceFrame (c k.val) ⟨p k.val,atlas.inside (c k.val) (inside k.val)⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame (c (k.val+1)).val (p (k.val+1)).val
        (atlas.inside (c (k.val+1)) (inside (k.val+1))).2
        (system.euclideanReferenceFrame (c (k.val+1))
          ⟨p (k.val+1),atlas.inside (c (k.val+1)) (inside (k.val+1))⟩)
      ∀ z ∈ closedBall 0 agreementRadius,
        H k z = centered L R ((chartAt E (c k.val).val) (p k.val).val)
          ((chartAt E (c (k.val+1)).val) (p (k.val+1)).val)
          (chartAt E (c (k.val+1)).val ∘ F.family ε (control k).val ∘
            (chartAt E (c k.val).val).symm) z) →
    ∀ z, g z ≠ 0 →
      ‖z‖ ≤ rowRadius ∧
      ‖OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N z‖ ≤ rowRadius ∧
      ∃ m : M, z = κ 0 m ∧
        (∀ k ≤ N, CylinderPrincipalCoefficient.prefixOrbit
          (fun j : Fin N => F.family ε (control j).val) (fun j => j) k m ∈
            (chartAt E (c k).val).source) ∧
        (∀ k < N, κ k (CylinderPrincipalCoefficient.prefixOrbit
          (fun j : Fin N => F.family ε (control j).val) (fun j => j) k m) ∈
            ball 0 agreementRadius) := by
  dsimp only
  intro H agreement z nonzero
  let c := AdaptedTubeWord.center atlas s labels
  let p := AdaptedTubeWord.reference atlas s labels
  let inside := AdaptedTubeWord.reference_mem atlas s labels
  let κ := AdaptedTubeWord.chart atlas s labels
  let points := fun (m : M) (j : Fin (N+1)) => CylinderPrincipalCoefficient.prefixOrbit
    (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m
  have target : z ∈ (κ 0).target := by
    by_contra outside
    dsimp only [κ] at outside
    exact nonzero (by simp only [ChartLocalization.coordinate,ite_eq_right outside])
  dsimp only [κ] at target
  let m := (κ 0).symm z
  have nz : FiniteSmoothCapturePartition.wordCutoff d (points m) labels ≠ 0 := by
    intro zero
    apply nonzero
    simp only [ChartLocalization.coordinate,ite_eq_left target]
    change (FiniteSmoothCapturePartition.wordCutoff d (points m) labels : ℂ)*amplitude m = 0
    rw [zero,Complex.ofReal_zero,zero_mul]
  have tracked (j : Fin (N+1)) : points m j ∈
      (atlas.normalizedTubeChart (labels j).val).source ∧
      atlas.normalizedTubeChart (labels j).val (points m j) ∈ ball 0 radius :=
    FiniteSmoothCapturePartition.wordCutoff_nonzero_mem d (points m) labels nz j
  have validity (k : ℕ) (hk : k ≤ N) : CylinderPrincipalCoefficient.prefixOrbit
      (fun j : Fin N => F.family ε (control j).val) (fun j => j) k m ∈
        (chartAt E (c k).val).source := by
    let j : Fin (N+1) := ⟨k,Nat.lt_succ_of_le hk⟩
    have member := (tracked j).1
    rw [←AdaptedTubeWord.chart_eq atlas s labels j] at member
    exact member
  have trackingAll (k : ℕ) (hk : k ≤ N) : κ k (CylinderPrincipalCoefficient.prefixOrbit
      (fun j : Fin N => F.family ε (control j).val) (fun j => j) k m) ∈ ball 0 radius := by
    let j : Fin (N+1) := ⟨k,Nat.lt_succ_of_le hk⟩
    have member := (tracked j).2
    rw [←AdaptedTubeWord.chart_eq atlas s labels j] at member
    exact member
  have tracking (k : ℕ) (hk : k < N) : κ k (CylinderPrincipalCoefficient.prefixOrbit
      (fun j : Fin N => F.family ε (control j).val) (fun j => j) k m) ∈
        ball 0 agreementRadius :=
    (ball_subset_ball smallAgreement) (trackingAll k (Nat.le_of_lt hk))
  have encode : κ 0 m = z := (κ 0).right_inv target
  have smallZ : ‖z‖ ≤ rowRadius := by
    have member := trackingAll 0 (Nat.zero_le N)
    change κ 0 m ∈ ball 0 radius at member
    rw [encode] at member
    exact (mem_ball_zero_iff.mp member).le.trans smallRow
  have wordEq := F.adapted_extension_word_eq atlas ε control c p inside agreementRadius H agreement m
    validity (fun k hk => mem_closedBall.mpr (mem_ball.mp (tracking k hk)).le) N le_rfl
  change OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N (κ 0 m) =
    κ N (CylinderPrincipalCoefficient.prefixOrbit
      (fun j : Fin N => F.family ε (control j).val) (fun j => j) N m) at wordEq
  have smallW : ‖OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N z‖ ≤
      rowRadius := by
    rw [←encode,wordEq]
    exact (mem_ball_zero_iff.mp (trackingAll N le_rfl)).le.trans smallRow
  exact ⟨smallZ,smallW,m,encode.symm,validity,tracking⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
