module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseFixedEuclideanPrototypes
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseJointCenteredHomeomorphs
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedEuclideanDomains
public import LeanShared.Geometry.NormalizedRegularChartBallExtension
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCones
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedHolderTube
public import LeanShared.Analysis.AffineCutoffHolderGlobalization
public import LeanShared.Analysis.AffineExtensionBounds
public import LeanShared.Analysis.InverseDerivativeHolder
import Mathlib.Tactic.Linarith

/-! One actual family has fixed prototypes before the controls, open
joint C1 forward and inverse maps, full fractional regularity, common
Holder derivative bounds, and the strict original-rate cone actions. -/
public noncomputable section
open Set IsManifold Bundle Metric Filter
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.CenteredManifoldCoordinates
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

/-- Only actual noise and chart-reference parameters. -/
private structure JointHolderIndex {system : PatchSystem b}
    (atlas : ChartAtlas system) (cutoff : ℝ≥0) (η : ℝ) where
  noise : ℝ≥0
  positive : 0 < noise
  small : noise ≤ cutoff
  control : cube (ι := ι) noise
  source : Λ
  source_member : source ∈ atlas.centers
  target : Λ
  target_member : target ∈ atlas.centers
  start : Λ
  start_inside : start ∈ atlas.patch source
  finish : Λ
  finish_inside : finish ∈ atlas.patch target
  near : dist (T start.val) finish.val < η

set_option maxHeartbeats 1000000 in
theorem Maps.adapted_joint_holder_global_euclidean_extensions {r α : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (positiveα : 0 < α) (subunitα : α < 1)
    (lower : α+1 < r) (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    {system : PatchSystem b} (atlas : ChartAtlas system) :
    ∃ K > 0, ∀ margin : ℝ, 0 < margin → ∃ radius > 0, ∃ η > 0,
      ∃ cutoff : ℝ≥0, 0 < cutoff ∧ cutoff ≤ F.window ∧
      ∃ ρ : system.EuclideanModel → ℝ,
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ Metric.closedBall 0 radius ∧
      (∀ z ∈ Metric.closedBall 0 (radius/2), ρ z = 1) ∧
      ∃ C Cinv : ℝ, 0 ≤ C ∧ 0 ≤ Cinv ∧
      ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.euclideanReferenceFrame c ⟨x, atlas.inside c hx⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.euclideanReferenceFrame d ⟨y, atlas.inside d hy⟩)
      ∃ S : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ]
          EuclideanSpace ℝ (Fin system.framing.stableDimension),
      ∃ U : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ]
          EuclideanSpace ℝ (Fin system.framing.unstableDimension),
        ‖S.toContinuousLinearMap‖ ≤ system.rate ∧ ‖U.symm.toContinuousLinearMap‖ ≤ system.rate ∧
        ‖(system.euclideanDiagonal U S).toContinuousLinearMap‖ ≤ K ∧
        ‖(system.euclideanDiagonal U S).symm.toContinuousLinearMap‖ ≤ K ∧
        ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff →
        ∃ O : Set (Control (ι := ι)), IsOpen O ∧ (cube (ι := ι) ε : Set _) ⊆ O ∧
        ∃ H : Control (ι := ι) → system.EuclideanModel ≃ₜ system.EuclideanModel,
          (∀ control ∈ O, ∀ z, H control z = system.euclideanDiagonal U S z +
            ρ z • (centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
              (chartAt E d.val ∘ F.family ε control ∘ (chartAt E c.val).symm) z-
                system.euclideanDiagonal U S z)) ∧
          ContDiffOn ℝ 1 (fun q : Control (ι := ι) × system.EuclideanModel => H q.1 q.2) (O ×ˢ univ) ∧
          ContDiffOn ℝ 1 (fun q : Control (ι := ι) × system.EuclideanModel => (H q.1).symm q.2) (O ×ˢ univ) ∧
          ∀ control : cube (ι := ι) ε,
            FractionalManifoldRegularity.Regular (E := system.EuclideanModel) (F := system.EuclideanModel) r (H control.val) ∧
            FractionalManifoldRegularity.Regular (E := system.EuclideanModel) (F := system.EuclideanModel) r (H control.val).symm ∧
            (∀ z, ‖fderiv ℝ (H control.val) z-(system.euclideanDiagonal U S).toContinuousLinearMap‖ < margin) ∧
            (∀ z ∈ Metric.closedBall 0 (radius/2), H control.val z =
              centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
                (chartAt E d.val ∘ F.family ε control.val ∘ (chartAt E c.val).symm) z) ∧
            (∀ z, z ∉ Metric.closedBall 0 radius → H control.val z = system.euclideanDiagonal U S z) ∧
            (∀ z, ‖fderiv ℝ (H control.val) z‖ ≤ K+margin) ∧
            (∀ z, ‖fderiv ℝ (H control.val).symm z‖ ≤ 2*K) ∧
            (∀ z w, ‖fderiv ℝ (H control.val) z-fderiv ℝ (H control.val) w‖ ≤ C*‖z-w‖^α) ∧
            (∀ z w, ‖fderiv ℝ (H control.val).symm z-fderiv ℝ (H control.val).symm w‖ ≤ Cinv*‖z-w‖^α) ∧
            (∀ z, ‖fderiv ℝ (H control.val) z-(system.euclideanDiagonal U S).toContinuousLinearMap‖ <
              OrthogonalDiagonalRatePerturbation.radius system.rate K) ∧
            (∀ z v, v ≠ 0 → v ∈ ProjectionConeTransversality.cone system.euclideanSecondProjection 1 →
              fderiv ℝ (H control.val) z v ∈ interior (ProjectionConeTransversality.cone system.euclideanSecondProjection
                (ProjectionConeRateMargin.opening system.rate))) ∧
            (∀ z v, v ≠ 0 → v ∈ ProjectionConeTransversality.cone system.euclideanFirstProjection 1 →
              (fderiv ℝ (H control.val).symm (H control.val z)).adjoint v ∈
                interior (ProjectionConeTransversality.cone system.euclideanFirstProjection
                  (ProjectionConeRateMargin.opening system.rate))) := by
  classical
  have regularity : 1 ≤ r := by linarith
  have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using regularity)
  have forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T :=
    regularT.differentiable.of_le (by exact_mod_cast order)
  obtain ⟨K, positiveK, blocks⟩ := F.fixed_euclidean_prototypes regularity forward backward atlas
  refine ⟨K,positiveK,fun margin positiveMargin => ?_⟩
  have positiveCone := (OrthogonalDiagonalRatePerturbation.radius_bounds system.rate K
    system.rate_pos system.rate_lt_one positiveK.le).1
  let requested := min margin (OrthogonalDiagonalRatePerturbation.radius system.rate K)
  let κ : ℝ := min requested (1/(2*(K+1)))
  have positiveκ : 0 < κ := lt_min (lt_min positiveMargin positiveCone) (by positivity)
  have marginBound : κ ≤ margin := (min_le_left _ _).trans (min_le_left _ _)
  have coneBound : κ ≤ OrthogonalDiagonalRatePerturbation.radius system.rate K :=
    (min_le_left _ _).trans (min_le_right _ _)
  have halfMargin : K*κ ≤ 1/2 := by
    have estimate : κ*(2*(K+1)) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 2*(K+1))).mp (min_le_right _ _)
    nlinarith
  obtain ⟨δ, positiveδ, ρ, extensions⟩ :=
    exists_uniform_scaled_chart_extension_of_ball (E := E) (F := E)
      (P := system.EuclideanModel) (Q := system.EuclideanModel) (M := M) (N := M)
      regularity positiveκ positiveK.le
  obtain ⟨R₀, positiveR₀, η₀, positiveη₀, ε₀, positiveε₀, block⟩ := blocks δ positiveδ
  obtain ⟨R₁, positiveR₁, η₁, positiveη₁, ε₁, positiveε₁, cap, domain⟩ := F.adapted_euclidean_domains atlas
  obtain ⟨R₂, positiveR₂, η₂, positiveη₂, ε₂, positiveε₂, _cap₂, B₂, C₂,
      nonnegativeB₂, nonnegativeC₂, holderTube⟩ :=
    F.adapted_euclidean_holder_tube positiveα subunitα lower regularT atlas
  let radius : ℝ := min R₀ (min R₁ R₂)/4
  have positiveRadius : 0 < radius := div_pos (lt_min positiveR₀ (lt_min positiveR₁ positiveR₂)) (by norm_num)
  have four₀ : 4*radius ≤ R₀ := by dsimp only [radius]; linarith [min_le_left R₀ (min R₁ R₂)]
  have four₁ : 4*radius ≤ R₁ := by dsimp only [radius]; linarith [(min_le_right R₀ (min R₁ R₂)).trans (min_le_left R₁ R₂)]
  have four₂ : 4*radius ≤ R₂ := by dsimp only [radius]; linarith [(min_le_right R₀ (min R₁ R₂)).trans (min_le_right R₁ R₂)]
  have radius₀ : radius ≤ R₀ := by linarith
  have radius₁ : radius ≤ R₁ := by linarith
  obtain ⟨η₃, positiveη₃, ε₃, positiveε₃, forcing⟩ :=
    F.adapted_euclidean_forcing regularity forward atlas (δ*radius) (mul_pos positiveδ positiveRadius)
  let η := min η₀ (min η₁ (min η₂ η₃))
  let cutoff := min ε₀ (min ε₁ (min ε₂ ε₃))
  have positiveη : 0 < η := lt_min positiveη₀ (lt_min positiveη₁ (lt_min positiveη₂ positiveη₃))
  have positiveCutoff : 0 < cutoff := lt_min positiveε₀ (lt_min positiveε₁ (lt_min positiveε₂ positiveε₃))
  have cutoffWindow : cutoff ≤ F.window :=
    (min_le_right _ _).trans ((min_le_left _ _).trans cap)
  obtain ⟨smoothρ, compactρ, supportρ, oneρ, extend⟩ := extensions radius positiveRadius
  let I := JointHolderIndex (ι := ι) atlas cutoff η ×
    {A : system.EuclideanModel →L[ℝ] system.EuclideanModel // ‖A‖ ≤ K}
  let L₀ (p : I) := ContinuousCenteredFrameCharts.chartFrame p.1.source.val p.1.start.val
    (atlas.inside p.1.source p.1.start_inside).2
    (system.euclideanReferenceFrame p.1.source ⟨p.1.start, atlas.inside p.1.source p.1.start_inside⟩)
  let R₃ (p : I) := ContinuousCenteredFrameCharts.chartFrame p.1.target.val p.1.finish.val
    (atlas.inside p.1.target p.1.finish_inside).2
    (system.euclideanReferenceFrame p.1.target ⟨p.1.finish, atlas.inside p.1.target p.1.finish_inside⟩)
  let h (p : I) := centered (L₀ p) (R₃ p) ((chartAt E p.1.source.val) p.1.start.val)
    ((chartAt E p.1.target.val) p.1.finish.val)
    (chartAt E p.1.target.val ∘ F.family p.1.noise p.1.control.val ∘ (chartAt E p.1.source.val).symm)
  have noise₁ (p : I) : p.1.noise ≤ ε₁ := p.1.small.trans ((min_le_right _ _).trans (min_le_left _ _))
  have noise₂ (p : I) : p.1.noise ≤ ε₂ := p.1.small.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have noise₃ (p : I) : p.1.noise ≤ ε₃ := p.1.small.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have near₁ (p : I) : dist (T p.1.start.val) p.1.finish.val < η₁ :=
    p.1.near.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have near₂ (p : I) : dist (T p.1.start.val) p.1.finish.val < η₂ := p.1.near.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have near₃ (p : I) : dist (T p.1.start.val) p.1.finish.val < η₃ := p.1.near.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have validity₀ (p : I) := domain p.1.noise p.1.positive (noise₁ p) p.1.control
    p.1.source p.1.source_member p.1.target p.1.target_member p.1.start p.1.start_inside
    p.1.finish p.1.finish_inside (near₁ p)
  have center (p : I) : ‖h p 0‖ ≤ δ*radius :=
    (forcing p.1.noise p.1.positive (noise₃ p) p.1.control p.1.source p.1.source_member p.1.target
      p.1.target_member p.1.start p.1.start_inside p.1.finish p.1.finish_inside (near₃ p)).le
  have mapRegular (p : I) := F.map_regular p.1.noise p.1.positive ((noise₁ p).trans cap) p.1.control
  have localRegular (p : I) : ContDiffOn ℝ 1 (h p) (ball 0 (3*radius)) := by
    intro z hz
    have small : ‖z‖ ≤ R₁ := by have normZ := mem_ball_zero_iff.mp hz; linarith
    have chartValid := validity₀ p z small
    exact ((contDiffAt_centered_charts (mapRegular p) _ _
      (chart_mem_maximalAtlas p.1.source.val) (chart_mem_maximalAtlas p.1.target.val)
      (L₀ p) (R₃ p) _ _ z chartValid.1 chartValid.2).of_le (by exact_mod_cast order)).contDiffWithinAt
  have ballInside : closedBall (0 : system.EuclideanModel) (2*radius) ⊆ ball 0 (3*radius) :=
    closedBall_subset_ball (by linarith)
  have supportInside : tsupport (ρ radius) ⊆ interior (closedBall 0 (2*radius)) := by
    intro z hz
    apply ball_subset_interior_closedBall
    exact (closedBall_subset_ball (by linarith : radius < 2*radius)) (supportρ hz)
  have derivativeLocal (p : I) (z : system.EuclideanModel) (hz : z ∈ closedBall 0 (2*radius)) :
      ‖fderiv ℝ (h p) z-p.2.val‖ ≤ B₂+K := by
    have facts := holderTube p.1.noise p.1.positive (noise₂ p) p.1.control p.1.source p.1.source_member
      p.1.target p.1.target_member p.1.start p.1.start_inside p.1.finish p.1.finish_inside (near₂ p)
    exact (norm_sub_le _ _).trans (add_le_add (facts.1 z
      (by have normZ := mem_closedBall_zero_iff.mp hz; linarith)) p.2.property)
  have holderLocal (p : I) (z : system.EuclideanModel) (hz : z ∈ closedBall 0 (2*radius))
      (w : system.EuclideanModel) (hw : w ∈ closedBall 0 (2*radius)) :
      ‖fderiv ℝ (h p) z-fderiv ℝ (h p) w‖ ≤ C₂*‖z-w‖^α := by
    have facts := holderTube p.1.noise p.1.positive (noise₂ p) p.1.control p.1.source p.1.source_member
      p.1.target p.1.target_member p.1.start p.1.start_inside p.1.finish p.1.finish_inside (near₂ p)
    exact facts.2 z (by have normZ := mem_closedBall_zero_iff.mp hz; linarith)
      w (by have normW := mem_closedBall_zero_iff.mp hw; linarith)
  obtain ⟨_Lip, C, nonnegativeC, controls⟩ := AffineCutoffHolderGlobalization.exists_controls
    (ρ radius) (smoothρ.of_le (by simp)) compactρ (show 0 < 2*radius by positivity)
    isOpen_ball ballInside supportInside h (fun p => p.2.val) (fun _ => 0)
    localRegular positiveα.le subunitα.le (mul_nonneg positiveδ.le positiveRadius.le)
    (add_nonneg nonnegativeB₂ positiveK.le) nonnegativeC₂
    (by simpa only [sub_zero] using center) derivativeLocal holderLocal
  let Cinv : ℝ := (2*K)*C*(2*K)^α*(2*K)
  have nonnegativeCinv : 0 ≤ Cinv := by dsimp only [Cinv]; positivity
  refine ⟨radius,positiveRadius,η,positiveη,cutoff,positiveCutoff,cutoffWindow,
    ρ radius,smoothρ,compactρ,supportρ,oneρ,C,Cinv,nonnegativeC,nonnegativeCinv,?_⟩
  intro c hc d hd x hx y hy near
  have close₀ : dist (T x.val) y.val < η₀ := near.trans_le (min_le_left _ _)
  have close₁ : dist (T x.val) y.val < η₁ := near.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have close₃ : dist (T x.val) y.val < η₃ := near.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨S,U,boundS,boundU,boundA,boundInv,derivative⟩ := block c hc d hd x hx y hy close₀
  dsimp only
  refine ⟨S,U,boundS,boundU,boundA,boundInv,?_⟩
  intro ε hp hw
  have hw₀ : ε ≤ ε₀ := hw.trans (min_le_left _ _)
  have hw₁ : ε ≤ ε₁ := hw.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hw₃ : ε ≤ ε₃ := hw.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
    (system.euclideanReferenceFrame c ⟨x, atlas.inside c hx⟩)
  let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
    (system.euclideanReferenceFrame d ⟨y, atlas.inside d hy⟩)
  let A := system.euclideanDiagonal U S
  have pointwise (control : cube (ι := ι) ε) := extend A boundInv 0 L R
    ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
    (chartAt E c.val) (chartAt E d.val) (chart_mem_maximalAtlas c.val)
    (chart_mem_maximalAtlas d.val) (F.family ε control.val) (F.map_regular ε hp (hw₁.trans cap) control)
    (fun z hz => domain ε hp hw₁ control c hc d hd x hx y hy close₁ z
      ((by simpa only [Metric.mem_closedBall,dist_zero_right] using hz : ‖z‖ ≤ radius).trans radius₁))
    (by simpa only [sub_zero] using (forcing ε hp hw₃ control c hc d hd x hx y hy close₃).le)
    (fun z hz => (derivative ε hp hw₀ control z
      ((by simpa only [Metric.mem_closedBall,dist_zero_right] using hz : ‖z‖ ≤ radius).trans radius₀)).2)
  choose H₀ formula regularH regularInv bound inside outside using pointwise
  let k : ℝ≥0 := ⟨κ,positiveκ.le⟩
  have threshold : κ < (‖A.symm.toContinuousLinearMap‖+1)⁻¹ := by
    have halfEq : 1/(2*(K+1)) = (K+1)⁻¹/2 := by field_simp
    have halfSmall : 1/(2*(K+1)) < (K+1)⁻¹ := by
      rw [halfEq]
      linarith [inv_pos.mpr (show 0 < K+1 by linarith)]
    have inverseBoundA : ‖A.symm.toContinuousLinearMap‖ ≤ K := boundInv
    have inverseThreshold : (K+1)⁻¹ ≤ (‖A.symm.toContinuousLinearMap‖+1)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le
        (show 0 < ‖A.symm.toContinuousLinearMap‖+1 by positivity) (by linarith : ‖A.symm.toContinuousLinearMap‖+1 ≤ K+1)
    exact ((min_le_right requested (1/(2*(K+1)))).trans_lt halfSmall).trans_le inverseThreshold
  have small := CutoffAffineDiffeomorphism.small_of_inflated A k threshold
  have validity (control : cube (ι := ι) ε) (z : system.EuclideanModel) (hz : z ∈ tsupport (ρ radius)) :=
    domain ε hp hw₁ control c hc d hd x hx y hy close₁ z
      ((by simpa only [Metric.mem_closedBall,dist_zero_right] using supportρ hz : ‖z‖ ≤ radius).trans radius₁)
  have familyEq (control : cube (ι := ι) ε) :
      (fun z => A z+0+ρ radius z •
        (centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
          (chartAt E d.val ∘ F.family ε control.val ∘ (chartAt E c.val).symm) z-(A z+0))) =
        (H₀ control : system.EuclideanModel → system.EuclideanModel) := by
    funext z
    exact (formula control z).symm
  obtain ⟨O,openO,contains,H,actual,joint,jointInverse⟩ := F.joint_centered_homeomorphs ε hp (hw₁.trans cap)
    (chartAt E c.val) (chartAt E d.val) (chart_mem_maximalAtlas c.val) (chart_mem_maximalAtlas d.val)
    L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val) A 0 (ρ radius)
    (smoothρ.of_le (by simp)) compactρ validity k (by exact_mod_cast positiveκ) small
    (fun control z => by rw [familyEq control]; exact bound control z)
  refine ⟨O,openO,contains,H,?_,joint,jointInverse,?_⟩
  · simpa only [add_zero] using actual
  · intro control
    have same : H control.val = H₀ control := by
      apply Homeomorph.ext
      intro z
      exact (actual control.val (contains control.property) z).trans (formula control z).symm
    rw [same]
    have smoothH : Differentiable ℝ (H₀ control) :=
      (regularH control).differentiable.contDiff.differentiable (by exact_mod_cast (Nat.ne_of_gt order))
    have smoothInv : Differentiable ℝ (H₀ control).symm :=
      (regularInv control).differentiable.contDiff.differentiable (by exact_mod_cast (Nat.ne_of_gt order))
    have inverseBounds := AffineExtensionBounds.inverse_uniform_bounds (H₀ control) A
      smoothH positiveK.le positiveκ.le boundInv halfMargin (fun z => (bound control z).le)
    let p : I := (⟨ε,hp,hw,control,c,hc,d,hd,x,hx,y,hy,near⟩,⟨A.toContinuousLinearMap,boundA⟩)
    have globalHolder (z w : system.EuclideanModel) :
        ‖fderiv ℝ (H₀ control) z-fderiv ℝ (H₀ control) w‖ ≤ C*‖z-w‖^α := by
      have sameFormula : (H₀ control : system.EuclideanModel → system.EuclideanModel) =
          fun v => A v+0+ρ radius v • (h p v-(A.toContinuousLinearMap v+0)) := funext (formula control)
      rw [sameFormula]
      exact AffineCutoffHolderGlobalization.affine_derivative_holder A.toContinuousLinearMap 0
        (controls p).1 (controls p).2.2.2.2 z w
    have inverseHolder (z w : system.EuclideanModel) :
        ‖fderiv ℝ (H₀ control).symm z-fderiv ℝ (H₀ control).symm w‖ ≤ Cinv*‖z-w‖^α := by
      exact InverseDerivativeHolder.bound convex_univ
        (fun y _ => smoothH ((H₀ control).symm y)) (fun y _ => smoothInv y)
        (fun _ _ => Eventually.of_forall (fun y => (H₀ control).symm_apply_apply y))
        (fun _ _ => Eventually.of_forall (fun y => (H₀ control).apply_symm_apply y))
        positiveα.le (by positivity) nonnegativeC (fun y _ => inverseBounds.2 y)
        (fun y _ z _ => globalHolder _ _) z (mem_univ _) w (mem_univ _)
    have coneDerivative (z : system.EuclideanModel) :
        ‖fderiv ℝ (H₀ control) z-(system.euclideanDiagonal U S).toContinuousLinearMap‖ <
          OrthogonalDiagonalRatePerturbation.radius system.rate K := (bound control z).trans_le coneBound
    have actions := system.actual_global_cones positiveK.le U S boundS boundU boundInv (H₀ control)
      smoothH smoothInv (fun z => (coneDerivative z).le)
    refine ⟨regularH control,regularInv control,fun z => (bound control z).trans_le marginBound,
      inside control,?_,?_,inverseBounds.2,globalHolder,inverseHolder,coneDerivative,actions⟩
    · simpa only [add_zero] using outside control
    · exact AffineExtensionBounds.derivative_norm_le (H₀ control) A.toContinuousLinearMap boundA
        (fun z => (bound control z).le.trans marginBound)


end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
