module

public import LeanShared.Geometry.MovingKernelLogJacobian

/-! Hölder moving projections and Hölder differential matrices give a
Hölder genuine logarithmic kernel-volume ratio. Local frames, their
invertibility and logarithmic determinant regularity are derived inside
the proof, rather than supplied as a moving-volume estimate. -/
public noncomputable section
namespace LeanShared.MovingKernelLogJacobian
open Set Filter
open scoped Topology ContDiff
variable {X E F G : Type*} [MetricSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

set_option maxHeartbeats 1800000 in
theorem exists_local_holder (S : Set X) (x : X) (hx : x ∈ S)
    (P : X → E →L[ℝ] E) (A : X → E →L[ℝ] F) (B : X → E →L[ℝ] G)
    (continuousP : ContinuousWithinAt P S x) (continuousA : ContinuousWithinAt A S x)
    (continuousB : ContinuousWithinAt B S x)
    (idempotent : ∀ y ∈ S, ∀ v, P y (P y v) = P y v)
    (injectiveA : ∀ y ∈ S, Function.Injective ((A y).comp (P y).ker.subtypeL))
    (injectiveB : ∀ y ∈ S, Function.Injective ((B y).comp (P y).ker.subtypeL))
    (α CP CA CB : ℝ) (nonnegativeP : 0 ≤ CP) (nonnegativeA : 0 ≤ CA) (nonnegativeB : 0 ≤ CB)
    (holderP : ∀ y ∈ S, ∀ z ∈ S, ‖P y - P z‖ ≤ CP * dist y z ^ α)
    (holderA : ∀ y ∈ S, ∀ z ∈ S, ‖A y - A z‖ ≤ CA * dist y z ^ α)
    (holderB : ∀ y ∈ S, ∀ z ∈ S, ‖B y - B z‖ ≤ CB * dist y z ^ α) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ H ≥ 0,
      ∀ y ∈ S ∩ U, ∀ z ∈ S ∩ U,
        |Real.log (ratio (P y) (A y) (B y)) - Real.log (ratio (P z) (A z) (B z))| ≤
          H * dist y z ^ α := by
  let params := fun y => (P y, A y, B y)
  have smooth : ContDiffAt ℝ 1 (framedLog (P x)) (params x) :=
    (framedLog_contDiffAt (P x) (A x) (B x) (idempotent x hx) (injectiveA x hx) (injectiveB x hx)).of_le (by simp)
  obtain ⟨L, W, neighborhood, lipschitz⟩ := smooth.exists_lipschitzOnWith
  have parameterContinuous : ContinuousWithinAt params S x :=
    continuousP.prodMk (continuousA.prodMk continuousB)
  have nearW : ∀ᶠ y in nhdsWithin x S, params y ∈ W := parameterContinuous.eventually neighborhood
  have centered : ‖P x - P x‖ * (2 * ‖P x‖ + 1) < 1 := by simp
  have nearSmall : ∀ᶠ y in nhdsWithin x S, ‖P x - P y‖ * (2 * ‖P x‖ + 1) < 1 :=
    ((continuousWithinAt_const.sub continuousP).norm.mul continuousWithinAt_const).eventually
      (gt_mem_nhds centered)
  obtain ⟨V, neighborhoodV, safeV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (nearW.and nearSmall)
  obtain ⟨U, contained, openU, memberU⟩ := mem_nhds_iff.mp neighborhoodV
  refine ⟨U, openU, memberU, (L : ℝ) * (CP + CA + CB), by positivity, ?_⟩
  intro y hy z hz
  have safeY := safeV ⟨contained hy.2, hy.1⟩
  have safeZ := safeV ⟨contained hz.2, hz.1⟩
  have formulaY := log_ratio_eq (P x) (P y) (A y) (B y) (idempotent x hx)
    (idempotent y hy.1) safeY.2 (injectiveA y hy.1) (injectiveB y hy.1)
  have formulaZ := log_ratio_eq (P x) (P z) (A z) (B z) (idempotent x hx)
    (idempotent z hz.1) safeZ.2 (injectiveA z hz.1) (injectiveB z hz.1)
  have parameterBound : ‖params y - params z‖ ≤ (CP + CA + CB) * dist y z ^ α := by
    have nonnegative : 0 ≤ dist y z ^ α := Real.rpow_nonneg dist_nonneg _
    have first := holderP y hy.1 z hz.1
    have other := holderA y hy.1 z hz.1
    have last := holderB y hy.1 z hz.1
    change max ‖P y - P z‖ (max ‖A y - A z‖ ‖B y - B z‖) ≤ _
    apply max_le
    · exact first.trans (mul_le_mul_of_nonneg_right (by linarith) nonnegative)
    · apply max_le
      · exact other.trans (mul_le_mul_of_nonneg_right (by linarith) nonnegative)
      · exact last.trans (mul_le_mul_of_nonneg_right (by linarith) nonnegative)
  have estimate := lipschitz.dist_le_mul (params y) safeY.1 (params z) safeZ.1
  have weighted := mul_le_mul_of_nonneg_left parameterBound L.coe_nonneg
  rw [formulaY, formulaZ]
  have converted : |framedLog (P x) (params y) - framedLog (P x) (params z)| ≤
      (L : ℝ) * ‖params y - params z‖ := by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using estimate
  exact converted.trans (by simpa only [mul_assoc] using weighted)

end LeanShared.MovingKernelLogJacobian
