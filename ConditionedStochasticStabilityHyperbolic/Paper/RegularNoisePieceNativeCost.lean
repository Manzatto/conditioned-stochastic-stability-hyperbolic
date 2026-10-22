module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseStrictNativeCostCollar

/-! The amplitude of one localized piece is bounded by its own strict-collar
coefficient times the actual native unstable Jacobian. The killing and
terminal cutoffs already enter that coefficient, and the pressure-centre
cutoff has absolute value at most one; a nonzero piece starts in the closed collar and in the support of its pressure-centre
cutoff, where the coefficient is a supremum. -/
@[expose] public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators NNReal ENNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared HyperbolicBasicSet FiniteSmoothCapturePartition PressureCoverRefinement
open LeanShared.FiniteJetComposition
variable {E M I Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [Fintype I] [Fintype Y]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {v : I → Set M}

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] [Fintype I] [Fintype Y]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem continuous_word (maps : ℕ → M → M) (continuousMaps : ∀ n, Continuous (maps n)) (k : ℕ) :
    Continuous (word maps k) := by
  induction k with
  | zero => exact continuous_id
  | succ k ih => exact (continuousMaps k).comp ih

omit [CompactSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem nativeDet_congr {h : HyperbolicData (E := E) T Λ} (a : h.NormedAdaptedProjection)
    {f₁ f₂ : M → M} (same : f₁ = f₂) (x : M) :
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f₁ x).toLinearMap.domRestrict (a.unstable x)).normDet =
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f₂ x).toLinearMap.domRestrict (a.unstable x)).normDet := by
  subst same; rfl

set_option maxHeartbeats 800000 in
theorem piece_native_cost_bound {h : HyperbolicData (E := E) T Λ} (a : h.NormedAdaptedProjection)
    (d : Data (E := E) Λ v) {Kp : Set M} {vp : Y → Set M} (p : Data (E := E) Kp vp) (y : Y)
    (χ g τ : M → ℝ) (continuousχ : Continuous χ) (continuousg : Continuous g)
    (continuousτ : Continuous τ)
    (W : Set M) (supportχ : tsupport χ ⊆ W) (collar : closure W ⊆ a.collar)
    (maps : ℕ → M → M) (continuousMaps : ∀ n, Continuous (maps n)) {N : ℕ} (hN : 0 < N)
    (labels : Fin (N+1) → I)
    (native : M ≃ₜ M) (identity : (native : M → M) = word maps N)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 native)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) native.symm) (m : M) :
    ‖(p.beta y m : ℂ) * (wordCutoff d (fun k : Fin (N+1) => word maps k.val m) labels : ℂ) *
      (((∏ k ∈ Finset.range N, χ (word maps k m) * g (word maps k m)) : ℝ) : ℂ) *
        (τ (native m) : ℂ)‖ₑ ≤
    ENNReal.ofReal (domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
      (fun x => |τ (word maps N x)| * nativeWordCost a d (fun x => χ x * g x) maps N labels x)) *
    ENNReal.ofReal ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) native m).toLinearMap.domRestrict
      (a.unstable m)).normDet := by
  classical
  let K := closure W ∩ tsupport (p.beta y)
  let det := fun x => ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) native x).toLinearMap.domRestrict
    (a.unstable x)).normDet
  have positive (x : M) : 0 < det x :=
    a.nativeJacobian_pos native (forward.mdifferentiable one_ne_zero) inverse x
  let cutoffWord := fun x => wordCutoff d (fun k : Fin (N+1) => word maps k.val x) labels
  let weight := fun x => ∏ k ∈ Finset.range N, χ (word maps k x) * g (word maps k x)
  let f := fun x => |τ (word maps N x)| * nativeWordCost a d (fun x => χ x * g x) maps N labels x
  have formula (x : M) : f x = |τ (native x)| * cutoffWord x * |weight x| / det x := by
    simp only [f, nativeWordCost, cutoffWord, weight, det, nativeDet_congr a identity x]
    rw [identity]
    ring
  have continuousCutoff : Continuous cutoffWord := by
    apply continuous_finsetProd
    intro k _
    exact (d.smooth (labels k)).continuous.comp (continuous_word maps continuousMaps k.val)
  have continuousWeight : Continuous weight := by
    apply continuous_finsetProd
    intro k _
    exact (continuousχ.comp (continuous_word maps continuousMaps k)).mul
      (continuousg.comp (continuous_word maps continuousMaps k))
  have numerator : Continuous (fun x => |τ (native x)| * cutoffWord x * |weight x|) :=
    ((continuousτ.comp native.continuous).abs.mul continuousCutoff).mul continuousWeight.abs
  have continuousF : ContinuousOn f a.collar := by
    have ratio := a.continuousOn_nativeRatio native forward inverse _ numerator
    exact ratio.congr (fun x _ => formula x)
  have compactK : IsCompact K := (isClosed_closure.inter (isClosed_tsupport _)).isCompact
  have insideK : K ⊆ a.collar := inter_subset_left.trans collar
  have bounded : BddAbove ({0} ∪ f '' (K ∩ univ)) :=
    (isCompact_singleton.union (compactK.image_of_continuousOn (continuousF.mono insideK))).bddAbove.mono
      (union_subset_union_right _ (image_mono inter_subset_left))
  have coefficientNonneg : 0 ≤ domainCoefficient K univ f :=
    le_csSup bounded (Or.inl (mem_singleton 0))
  by_cases zero : (p.beta y m : ℂ) * (cutoffWord m : ℂ) * ((weight m : ℝ) : ℂ) *
      (τ (native m) : ℂ) = 0
  · change ‖(p.beta y m : ℂ) * (cutoffWord m : ℂ) * ((weight m : ℝ) : ℂ) *
      (τ (native m) : ℂ)‖ₑ ≤ _
    rw [zero, enorm_zero]
    exact zero_le
  have pressureNonzero : p.beta y m ≠ 0 := by
    intro hz; apply zero; simp [hz]
  have weightNonzero : weight m ≠ 0 := by
    intro hz; apply zero; simp [hz]
  have killingNonzero : χ m ≠ 0 := by
    intro hz
    apply weightNonzero
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hN)
    simp [word, hz]
  have memberK : m ∈ K :=
    ⟨subset_closure (supportχ (subset_tsupport χ killingNonzero)),
      subset_tsupport _ pressureNonzero⟩
  have valueLe : f m ≤ domainCoefficient K univ f :=
    le_csSup bounded (Or.inr ⟨m, ⟨memberK, mem_univ m⟩, rfl⟩)
  have realBound : ‖(p.beta y m : ℂ) * (cutoffWord m : ℂ) * ((weight m : ℝ) : ℂ) *
      (τ (native m) : ℂ)‖ ≤ domainCoefficient K univ f * det m := by
    have normEq : ‖(p.beta y m : ℂ) * (cutoffWord m : ℂ) * ((weight m : ℝ) : ℂ) *
        (τ (native m) : ℂ)‖ = |p.beta y m| * |cutoffWord m| * |weight m| * |τ (native m)| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have pressureLe : |p.beta y m| ≤ 1 := by
      rw [abs_of_nonneg (p.bounds y m).1]; exact (p.bounds y m).2
    have cutoffNonneg : 0 ≤ cutoffWord m := wordCutoff_nonneg d _ labels
    have fDet : f m * det m = |τ (native m)| * cutoffWord m * |weight m| := by
      rw [formula m, div_mul_cancel₀ _ (positive m).ne']
    rw [normEq, abs_of_nonneg cutoffNonneg]
    calc |p.beta y m| * cutoffWord m * |weight m| * |τ (native m)|
        ≤ 1 * cutoffWord m * |weight m| * |τ (native m)| := by
          gcongr
      _ = f m * det m := by rw [fDet]; ring
      _ ≤ domainCoefficient K univ f * det m :=
          mul_le_mul_of_nonneg_right valueLe (positive m).le
  change ‖(p.beta y m : ℂ) * (cutoffWord m : ℂ) * ((weight m : ℝ) : ℂ) *
      (τ (native m) : ℂ)‖ₑ ≤ ENNReal.ofReal (domainCoefficient K univ f) * ENNReal.ofReal (det m)
  rw [← ofReal_norm, ← ENNReal.ofReal_mul coefficientNonneg]
  exact ENNReal.ofReal_le_ofReal realBound

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
