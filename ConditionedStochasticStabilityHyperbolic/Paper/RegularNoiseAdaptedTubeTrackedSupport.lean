module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeWordAmplitudeSupport
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeWordAmplitudeContinuity
public import LeanShared.Geometry.ChartedHomeomorphCoordinateMap
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedPhysicalCylinderSourceCoordinates

/-! Physical cylinder witnesses for an arbitrary localized amplitude along an
arbitrary reference word of adapted tubes. Tracking of every orbit point in
its tube is a hypothesis on the concrete amplitude; it need not come from a
single beta word. This allows the final reference chart to be the chart of an
independent terminal input slot, as required by the terminal cutoff
bookkeeping. -/
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

set_option maxHeartbeats 800000 in
theorem Maps.adapted_tubeWord_tracked_support {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (atlas : ChartAtlas system)
    {radius agreementRadius rowRadius : ℝ}
    (smallAgreement : radius ≤ agreementRadius) (smallRow : radius ≤ rowRadius)
    (s : Finset atlas.NormalizedTubeIndex)
    (ε : ℝ≥0) {N : ℕ} (control : Fin N → cube (ι := ι) ε)
    (labels : Fin (N+1) → s) (θ amplitude : M → ℂ)
    (track : ∀ m : M, θ m * amplitude m ≠ 0 → ∀ j : Fin (N+1),
      CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m ∈
          (atlas.normalizedTubeChart (labels j).val).source ∧
      atlas.normalizedTubeChart (labels j).val (CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m) ∈ ball 0 radius) :
    let c := AdaptedTubeWord.center atlas s labels
    let p := AdaptedTubeWord.reference atlas s labels
    let inside := AdaptedTubeWord.reference_mem atlas s labels
    let κ := AdaptedTubeWord.chart atlas s labels
    let g := ChartLocalization.coordinate (κ 0) θ amplitude
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
  have nz : θ m * amplitude m ≠ 0 := by
    intro zero
    apply nonzero
    simp only [ChartLocalization.coordinate,ite_eq_left target]
    exact zero
  have tracked (j : Fin (N+1)) : points m j ∈
      (atlas.normalizedTubeChart (labels j).val).source ∧
      atlas.normalizedTubeChart (labels j).val (points m j) ∈ ball 0 radius :=
    track m nz j
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


set_option maxHeartbeats 800000 in
/-- An open physical itinerary cylinder along an arbitrary reference word
contains the whole closed support of a localized amplitude, provided the
cutoff is supported in that cylinder. -/
theorem Maps.adapted_tubeWord_cylinder_open {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (atlas : ChartAtlas system)
    (radius : ℝ) (s : Finset atlas.NormalizedTubeIndex)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window)
    {N : ℕ} (control : Fin N → cube (ι := ι) ε)
    (labels : Fin (N+1) → s) (θ amplitude : M → ℂ)
    (continuousθ : Continuous θ) (continuousAmplitude : Continuous amplitude)
    (support : tsupport θ ⊆ ⋂ j : Fin (N+1),
      (fun m => CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m) ⁻¹'
          atlas.normalizedTube radius (labels j).val) :
    let κ := AdaptedTubeWord.chart atlas s labels
    let points := fun (m : M) (j : Fin (N+1)) => CylinderPrincipalCoefficient.prefixOrbit
      (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m
    let g := ChartLocalization.coordinate (κ 0) θ amplitude
    Continuous g ∧ HasCompactSupport g ∧
      ∃ O : Set system.EuclideanModel, IsOpen O ∧ O ⊆ (κ 0).target ∧ tsupport g ⊆ O ∧
      ∀ z ∈ O, ∃ m : M, z = κ 0 m ∧
        ∀ j : Fin (N+1), points m j ∈ atlas.normalizedTube radius (labels j).val := by
  let := F.atlas.compactSpace
  dsimp only
  let κ := AdaptedTubeWord.chart atlas s labels
  let points := fun (m : M) (j : Fin (N+1)) => CylinderPrincipalCoefficient.prefixOrbit
    (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m
  let g := ChartLocalization.coordinate (κ 0) θ amplitude
  have continuousPrefix (k : ℕ) : Continuous (CylinderPrincipalCoefficient.prefixOrbit
      (fun j : Fin N => F.family ε (control j).val) (fun j => j) k) := by
    induction k with
    | zero => exact continuous_id
    | succ k ih =>
      by_cases hk : k < N
      · simpa only [CylinderPrincipalCoefficient.prefixOrbit,dite_eq_left hk,Function.comp_def] using
          (F.map_regular ε positive window (control ⟨k,hk⟩)).differentiable.continuous.comp ih
      · simpa only [CylinderPrincipalCoefficient.prefixOrbit,dite_eq_right hk] using ih
  have continuousPoints (j : Fin (N+1)) : Continuous (fun m => points m j) := continuousPrefix j.val
  let cylinder := ⋂ j : Fin (N+1),
    (fun m => points m j) ⁻¹' atlas.normalizedTube radius (labels j).val
  have openCylinder : IsOpen cylinder := isOpen_iInter_of_finite (fun j =>
    (atlas.normalizedTube_open radius (labels j).val).preimage (continuousPoints j))
  have cylinderSource : cylinder ⊆ (κ 0).source := by
    intro m hm
    have member := (mem_iInter.mp hm (⟨0,Nat.zero_lt_succ N⟩ : Fin (N+1))).1
    rw [←AdaptedTubeWord.chart_eq atlas s labels (⟨0,Nat.zero_lt_succ N⟩ : Fin (N+1))] at member
    exact member
  have cutoffSource : tsupport θ ⊆ (κ 0).source := support.trans cylinderSource
  have compactCutoff : HasCompactSupport θ := HasCompactSupport.of_compactSpace θ
  have continuousG : Continuous g := ChartFractionalLocalization.continuous (κ 0) θ
    cutoffSource compactCutoff continuousθ continuousAmplitude
  have compactG : HasCompactSupport g :=
    ChartLocalization.coordinate_hasCompactSupport (κ 0) θ cutoffSource compactCutoff amplitude
  let O := (κ 0) '' cylinder
  have openO : IsOpen O := (κ 0).isOpen_image_of_subset_source openCylinder cylinderSource
  have targetO : O ⊆ (κ 0).target := by
    rintro _ ⟨m,hm,rfl⟩
    exact (κ 0).map_source (cylinderSource hm)
  have localCompact := ChartLocalization.localSupport_isCompact (κ 0) θ cutoffSource compactCutoff
  have localSupport : tsupport g ⊆ ChartLocalization.localSupport (κ 0) θ := by
    apply closure_minimal ?_ localCompact.isClosed
    intro z nonzero
    by_contra outside
    exact nonzero (ChartLocalization.coordinate_zero_outside (κ 0) θ amplitude z outside)
  refine ⟨continuousG,compactG,O,openO,targetO,localSupport.trans (image_mono support),?_⟩
  rintro z ⟨m,hm,rfl⟩
  exact ⟨m,rfl,fun j => mem_iInter.mp hm j⟩


set_option maxHeartbeats 800000 in
/-- On the open itinerary cylinder of an arbitrary reference word, the global
extension word agrees with the actual coordinate word from the first to the
last reference chart. This supplies the representation fields of the closed
physical output. -/
theorem Maps.adapted_tubeWord_output_agreement {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (atlas : ChartAtlas system)
    {radius agreementRadius : ℝ} (smallAgreement : radius ≤ agreementRadius)
    (s : Finset atlas.NormalizedTubeIndex)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window)
    {N : ℕ} (control : Fin N → cube (ι := ι) ε)
    (labels : Fin (N+1) → s) (θ amplitude : M → ℂ)
    (continuousθ : Continuous θ) (continuousAmplitude : Continuous amplitude)
    (support : tsupport θ ⊆ ⋂ j : Fin (N+1),
      (fun m => CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m) ⁻¹'
          atlas.normalizedTube radius (labels j).val) :
    let c := AdaptedTubeWord.center atlas s labels
    let p := AdaptedTubeWord.reference atlas s labels
    let inside := AdaptedTubeWord.reference_mem atlas s labels
    let κ := AdaptedTubeWord.chart atlas s labels
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
    ∀ native : M ≃ₜ M, (native : M → M) = CylinderPrincipalCoefficient.prefixOrbit
      (fun k : Fin N => F.family ε (control k).val) (fun k => k) N →
    ∃ O : Set system.EuclideanModel,
      tsupport (ChartLocalization.coordinate (κ 0) θ amplitude) ⊆ O ∧
      O ⊆ (ChartedHomeomorphCoordinateMap.coordinateMap (κ 0) (κ N) native).source ∧
      EqOn (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N)
        (ChartedHomeomorphCoordinateMap.coordinateMap (κ 0) (κ N) native) O := by
  dsimp only
  intro H agreement native identity
  let c := AdaptedTubeWord.center atlas s labels
  let p := AdaptedTubeWord.reference atlas s labels
  let inside := AdaptedTubeWord.reference_mem atlas s labels
  let κ := AdaptedTubeWord.chart atlas s labels
  obtain ⟨_,_,O,_,targetO,supportO,memberO⟩ := F.adapted_tubeWord_cylinder_open atlas radius s ε
    positive window control labels θ amplitude continuousθ continuousAmplitude support
  have zeroSource (m : M) (hm : CylinderPrincipalCoefficient.prefixOrbit
      (fun k : Fin N => F.family ε (control k).val) (fun k => k) 0 m ∈
        atlas.normalizedTube radius (labels ⟨0,Nat.zero_lt_succ N⟩).val) : m ∈ (κ 0).source := by
    have member := hm.1
    rw [←AdaptedTubeWord.chart_eq atlas s labels (⟨0,Nat.zero_lt_succ N⟩ : Fin (N+1))] at member
    exact member
  have lastSource (m : M) (hm : CylinderPrincipalCoefficient.prefixOrbit
      (fun k : Fin N => F.family ε (control k).val) (fun k => k) N m ∈
        atlas.normalizedTube radius (labels (Fin.last N)).val) :
      CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) N m ∈ (κ N).source := by
    have member := hm.1
    rw [←AdaptedTubeWord.chart_eq atlas s labels (Fin.last N)] at member
    exact member
  refine ⟨O,supportO,?_,?_⟩
  · intro z hz
    obtain ⟨m,rfl,tubes⟩ := memberO z hz
    rw [ChartedHomeomorphCoordinateMap.coordinateMap_source]
    refine ⟨targetO hz,?_⟩
    rw [(κ 0).left_inv (zeroSource m (tubes ⟨0,Nat.zero_lt_succ N⟩)), identity]
    exact lastSource m (tubes (Fin.last N))
  · intro z hz
    obtain ⟨m,rfl,tubes⟩ := memberO z hz
    have validity (k : ℕ) (hk : k ≤ N) : CylinderPrincipalCoefficient.prefixOrbit
        (fun j : Fin N => F.family ε (control j).val) (fun j => j) k m ∈
          (chartAt E (c k).val).source := by
      let j : Fin (N+1) := ⟨k,Nat.lt_succ_of_le hk⟩
      have member := (tubes j).1
      rw [←AdaptedTubeWord.chart_eq atlas s labels j] at member
      exact member
    have tracking (k : ℕ) (hk : k < N) : κ k (CylinderPrincipalCoefficient.prefixOrbit
        (fun j : Fin N => F.family ε (control j).val) (fun j => j) k m) ∈
          closedBall 0 agreementRadius := by
      let j : Fin (N+1) := ⟨k,Nat.lt_succ_of_le (Nat.le_of_lt hk)⟩
      have member := (tubes j).2
      rw [←AdaptedTubeWord.chart_eq atlas s labels j] at member
      exact mem_closedBall.mpr ((mem_ball.mp member).le.trans smallAgreement)
    have wordEq := F.adapted_extension_word_eq atlas ε control c p inside agreementRadius H agreement m
      validity tracking N le_rfl
    change OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N (κ 0 m) =
      κ N (CylinderPrincipalCoefficient.prefixOrbit
        (fun j : Fin N => F.family ε (control j).val) (fun j => j) N m) at wordEq
    rw [wordEq, ChartedHomeomorphCoordinateMap.coordinateMap_apply,
      (κ 0).left_inv (zeroSource m (tubes ⟨0,Nat.zero_lt_succ N⟩)), identity]


set_option maxHeartbeats 1600000 in
/-- The four principal-row support conditions, for a localized amplitude
supported in the open itinerary cylinder of an arbitrary reference word. -/
theorem Maps.adapted_tubeWord_principal_witness {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (atlas : ChartAtlas system)
    {radius agreementRadius rowRadius : ℝ}
    (smallAgreement : radius ≤ agreementRadius) (smallRow : radius ≤ rowRadius)
    (s : Finset atlas.NormalizedTubeIndex)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window)
    {N : ℕ} (control : Fin N → cube (ι := ι) ε)
    (labels : Fin (N+1) → s) (θ amplitude : M → ℂ)
    (support : tsupport θ ⊆ ⋂ j : Fin (N+1),
      (fun m => CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m) ⁻¹'
          atlas.normalizedTube radius (labels j).val) :
    let c := AdaptedTubeWord.center atlas s labels
    let p := AdaptedTubeWord.reference atlas s labels
    let inside := AdaptedTubeWord.reference_mem atlas s labels
    let κ := AdaptedTubeWord.chart atlas s labels
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
    ∀ native : M ≃ₜ M, (native : M → M) = CylinderPrincipalCoefficient.prefixOrbit
      (fun k : Fin N => F.family ε (control k).val) (fun k => k) N →
    let W := OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N
    let L := ContinuousCenteredFrameCharts.chartFrame (c 0).val (p 0).val
      (atlas.inside (c 0) (inside 0)).2
      (system.euclideanReferenceFrame (c 0) ⟨p 0, atlas.inside (c 0) (inside 0)⟩)
    let R := ContinuousCenteredFrameCharts.chartFrame (c N).val (p N).val
      (atlas.inside (c N) (inside N)).2
      (system.euclideanReferenceFrame (c N) ⟨p N, atlas.inside (c N) (inside N)⟩)
    ∀ z, ChartLocalization.coordinate (κ 0) θ amplitude z ≠ 0 →
      ‖z‖ ≤ rowRadius ∧ ‖W z‖ ≤ rowRadius ∧
      native (system.normalizedProjectionPoint (c 0) ⟨p 0, atlas.inside (c 0) (inside 0)⟩ z) =
        system.normalizedProjectionPoint (c N) ⟨p N, atlas.inside (c N) (inside N)⟩ (W z) ∧
      (W : system.EuclideanModel → system.EuclideanModel) =ᶠ[𝓝 z]
        centered L R ((chartAt E (c 0).val) (p 0).val) ((chartAt E (c N).val) (p N).val)
          (chartAt E (c N).val ∘ native ∘ (chartAt E (c 0).val).symm) := by
  dsimp only
  intro H agreement native identity z nonzero
  let c := AdaptedTubeWord.center atlas s labels
  let p := AdaptedTubeWord.reference atlas s labels
  let inside := AdaptedTubeWord.reference_mem atlas s labels
  let κ := AdaptedTubeWord.chart atlas s labels
  have track : ∀ m : M, θ m * amplitude m ≠ 0 → ∀ j : Fin (N+1),
      CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m ∈
          (atlas.normalizedTubeChart (labels j).val).source ∧
      atlas.normalizedTubeChart (labels j).val (CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m) ∈ ball 0 radius := by
    intro m hm j
    exact mem_iInter.mp (support (subset_tsupport θ (left_ne_zero_of_mul hm))) j
  obtain ⟨small,smallW,m,encode,valid,tracking⟩ := F.adapted_tubeWord_tracked_support atlas
    smallAgreement smallRow s ε control labels θ amplitude track H agreement z nonzero
  have target : z ∈ (κ 0).target := by
    rw [encode]
    exact (κ 0).map_source (valid 0 (Nat.zero_le N))
  have decode : (κ 0).symm z = m := by
    rw [encode]
    exact (κ 0).left_inv (valid 0 (Nat.zero_le N))
  have coordinates := F.adapted_physical_cylinder_source_coordinates atlas ε positive window control
    c p inside agreementRadius H agreement z target
    (by
      change ∀ k ≤ N, CylinderPrincipalCoefficient.prefixOrbit
        (fun j : Fin N => F.family ε (control j).val) (fun j => j) k ((κ 0).symm z) ∈ _
      rw [decode]
      exact valid)
    (by
      change ∀ k < N, κ k (CylinderPrincipalCoefficient.prefixOrbit
        (fun j : Fin N => F.family ε (control j).val) (fun j => j) k ((κ 0).symm z)) ∈ _
      rw [decode]
      exact tracking)
  rw [identity]
  exact ⟨small,smallW,coordinates.1,coordinates.2⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
