module

public import LeanShared.Dynamics.HyperbolicNativeChartRelations
public import LeanShared.Dynamics.FiniteAtlasProjectionHolder
public import LeanShared.Dynamics.BunchingExponent
public import LeanShared.Geometry.FiniteNativeCocycleHolder
public import LeanShared.Geometry.BundleEndomorphismCoordinateNorm
public import LeanShared.Geometry.BoundedRiemannianLipschitz
public import LeanShared.Geometry.FractionalOneJetIteration

/-! Hölder regularity of the actual stable projection on a hyperbolic core.
The finite native tangent atlas, block length, chart itineraries, matrix
regularity and bunching exponent are all constructed from the actual
fractionally differentiable diffeomorphism. Distances are those of the
constructed bounded Riemannian length metric, not an arbitrary compatible
ambient metric. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle FractionalManifoldRegularity
open scoped Manifold ContDiff Bundle NNReal

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

set_option maxHeartbeats 2400000 in
theorem HyperbolicData.exists_core_projection_holder
    (h : HyperbolicData (E := E) T Λ) {r : ℝ} (regularity : 1 < r)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm) :
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∃ centers : Finset Λ, ∃ patch : Λ → Set M,
      (∀ i, IsCompact (patch i) ∧ patch i ⊆ (chartAt E i.val).source) ∧
      Λ ⊆ ⋃ i ∈ centers, interior (patch i) ∧ ∃ H ≥ 0,
      ∀ i ∈ centers, ∀ x ∈ Λ, ∀ y ∈ Λ, x ∈ patch i → y ∈ patch i →
        ‖h.chartProjection i x - h.chartProjection i y‖ ≤
          H * (@dist M (BoundedRiemannianMetric.metric (E := E)).toDist x y) ^ β := by
  let a := min ((r - 1) / 2) (1 / 2)
  have positiveA : 0 < a := lt_min (by linarith) (by norm_num)
  have smallA : a < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have lowerA : a + 1 < r := by have := min_le_left ((r - 1) / 2) (1 / 2); dsimp only [a]; linarith
  have forward := forwardRegular.mdifferentiable regularity.le
  have inverse := inverseRegular.mdifferentiable regularity.le
  obtain ⟨centers, patch, C, positiveC, facts, cover, frames, N, positiveN,
    forwardBound, backwardBound, forwardInverseBound, backwardInverseBound⟩ :=
    h.exists_finite_inverse_chart_blocks forward inverse (1 / 8) (by norm_num)
  let S := T ^ N
  have smoothForward := DiffeomorphismIterates.mdifferentiable_pow T forward N
  have smoothInverse := DiffeomorphismIterates.mdifferentiable_symm_pow T inverse N
  have regF := forwardRegular.iterate_lower_one_add positiveA smallA lowerA N positiveN
  have regG := inverseRegular.iterate_lower_one_add positiveA smallA lowerA N positiveN
  obtain ⟨CF, nonnegativeCF, holderF⟩ := regF.finite_native_cocycle_holder positiveA smallA
    (fun i : ↥centers => i.val.val) (fun i => patch i.val)
    (fun i => (facts i.val).1) (fun i => (facts i.val).2)
  obtain ⟨CG, nonnegativeCG, holderG⟩ := regG.finite_native_cocycle_holder positiveA smallA
    (fun i : ↥centers => i.val.val) (fun i => patch i.val)
    (fun i => (facts i.val).1) (fun i => (facts i.val).2)
  have smoothF : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 ((T : M → M)^[N]) := by
    have floor : ⌊a + 1⌋₊ = 1 := by rw [Nat.floor_add_one positiveA.le, Nat.floor_eq_zero.mpr smallA]
    simpa only [floor, Nat.cast_one] using regF.differentiable
  have smoothG : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 ((T.symm : M → M)^[N]) := by
    have floor : ⌊a + 1⌋₊ = 1 := by rw [Nat.floor_add_one positiveA.le, Nat.floor_eq_zero.mpr smallA]
    simpa only [floor, Nat.cast_one] using regG.differentiable
  obtain ⟨LF, lipF⟩ := BoundedRiemannianMetric.exists_lipschitz _ smoothF
  obtain ⟨LG, lipG⟩ := BoundedRiemannianMetric.exists_lipschitz _ smoothG
  let L : ℝ≥0 := max (max LF LG) 1
  have positiveL : 0 < (L : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast le_max_right (max LF LG) 1)
  have small : 2 * (1 / 8 : ℝ) ^ 2 < 1 := by norm_num
  obtain ⟨β, positiveβ, lowerβ, _, bunched⟩ :=
    BunchedSectionHolder.exists_exponent (2 * (1 / 8) ^ 2) L a small positiveL positiveA
  obtain ⟨B, positiveB, nativeProjectionBound⟩ := h.exists_projection_norm_bound
  have preserves : MapsTo T Λ Λ := fun _ hx => h.invariant ▸ mem_image_of_mem T hx
  have inversePreserves : MapsTo T.symm Λ Λ := by
    intro x hx
    rw [← h.invariant] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [T.symm_apply_apply] using hy
  let F : Λ → Λ := fun x => ⟨(T : M → M)^[N] x, preserves.iterate N x.property⟩
  let G : Λ → Λ := fun x => ⟨(T.symm : M → M)^[N] x, inversePreserves.iterate N x.property⟩
  let corePatch : Λ → Set Λ := fun i => Subtype.val ⁻¹' patch i
  let P : Λ → Λ → E →L[ℝ] E := fun i x => h.chartProjection i x
  let A : Λ → Λ → Λ → E →L[ℝ] E := fun i j x => h.chartBlock N i j x
  let D : Λ → Λ → Λ → E →L[ℝ] E := fun i j x => h.chartInverseBlock N i j x
  let AI : Λ → Λ → Λ → E →L[ℝ] E := fun i j x =>
    inverseChartMap S smoothForward smoothInverse i.val j.val x
  let DI : Λ → Λ → Λ → E →L[ℝ] E := fun i j x =>
    inverseChartMap S.symm smoothInverse (by simpa only [Homeomorph.symm_symm] using smoothForward) i.val j.val x
  have chartMember (i : Λ) (x : Λ) (inside : x ∈ corePatch i) :
      x.val ∈ (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val).baseSet := by
    rw [TangentChartTrivialization.baseSet]
    exact (facts i).2 inside
  have bounded (i : Λ) (hi : i ∈ centers) (x : Λ) (inside : x ∈ corePatch i) :
      ‖P i x‖ ≤ C ^ 2 * B ∧ ‖1 - P i x‖ ≤ C ^ 2 * B := by
    have first := BundleEndomorphismCoordinates.norm_le (TangentSpace (𝓘(ℝ,E)))
      (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val) h.projection x C B positiveC.le
      (frames i hi x inside).1 (frames i hi x inside).2 (nativeProjectionBound x x.property).1
    have second := BundleEndomorphismCoordinates.norm_le (TangentSpace (𝓘(ℝ,E)))
      (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val)
      (fun y => ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ,E)) y) - h.projection y)
      x C B positiveC.le (frames i hi x inside).1 (frames i hi x inside).2 (nativeProjectionBound x x.property).2
    rw [BundleProjectionCocycleCoordinates.projection_complement _ _ h.projection x (chartMember i x inside)] at second
    exact ⟨first, second⟩
  have idem : ∀ i ∈ centers, ∀ x ∈ corePatch i, P i x * P i x = P i x :=
    fun i _ x hx => h.chartProjection_idempotent i x x.property ((facts i).2 hx)
  have inverseF : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ corePatch i,
      F x ∈ corePatch j → AI i j x * A i j x = 1 := by
    intro i hi j hj x hx target
    dsimp only [AI, A, S]
    unfold HyperbolicData.chartBlock
    rw [← DiffeomorphismIterates.coe_pow]
    exact inverseChartMap_left (T ^ N) smoothForward smoothInverse i.val j.val x ((facts i).2 hx)
      (by simpa only [DiffeomorphismIterates.coe_pow] using (facts j).2 target)
  have inverseG : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ corePatch i,
      G x ∈ corePatch j → DI i j x * D i j x = 1 := by
    intro i hi j hj x hx target
    dsimp only [DI, D, S]
    unfold HyperbolicData.chartInverseBlock
    rw [← DiffeomorphismIterates.coe_symm_pow]
    exact inverseChartMap_left (T ^ N).symm smoothInverse _ i.val j.val x ((facts i).2 hx)
      (by simpa only [DiffeomorphismIterates.coe_symm_pow] using (facts j).2 target)
  have invariantF : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ corePatch i,
      F x ∈ corePatch j → P j (F x) * A i j x = A i j x * P i x :=
    fun i _ j _ x hx target => h.chartBlock_intertwines forward N i j x x.property ((facts i).2 hx) ((facts j).2 target)
  have invariantG : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ corePatch i,
      G x ∈ corePatch j → (1 - P j (G x)) * D i j x = D i j x * (1 - P i x) :=
    fun i _ j _ x hx target => h.chartInverseBlock_intertwines forward inverse N i j x x.property ((facts i).2 hx) ((facts j).2 target)
  have boundF : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ corePatch i,
      F x ∈ corePatch j → ‖A i j x * P i x‖ ≤ 1 / 8 :=
    fun i hi j hj x hx target => forwardBound i hi j hj x x.property hx target
  have boundG : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ corePatch i,
      G x ∈ corePatch j → ‖D i j x * (1 - P i x)‖ ≤ 1 / 8 :=
    fun i hi j hj x hx target => backwardBound i hi j hj x x.property hx target
  have boundIF : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ corePatch i,
      F x ∈ corePatch j → ‖AI i j x * (1 - P j (F x))‖ ≤ 1 / 8 :=
    fun i hi j hj x hx target => forwardInverseBound i hi j hj x x.property hx target
  have boundIG : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ corePatch i,
      G x ∈ corePatch j → ‖DI i j x * P j (G x)‖ ≤ 1 / 8 :=
    fun i hi j hj x hx target => backwardInverseBound i hi j hj x x.property hx target
  have compactCore : CompactSpace Λ := isCompact_iff_compactSpace.mp h.compact
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  let _ : CompactSpace Λ := compactCore
  have coreCover : (univ : Set Λ) ⊆ ⋃ i ∈ centers, interior (corePatch i) := by
    intro x _
    obtain ⟨i, selected, inside⟩ := mem_iUnion₂.mp (cover x.property)
    exact mem_iUnion₂.mpr ⟨i, selected, preimage_interior_subset_interior_preimage continuous_subtype_val inside⟩
  have fLip : LipschitzWith L F := by
    intro x y
    exact (lipF.weaken ((le_max_left LF LG).trans (le_max_left _ _))) x.val y.val
  have gLip : LipschitzWith L G := by
    intro x y
    exact (lipG.weaken ((le_max_right LF LG).trans (le_max_left _ _))) x.val y.val
  have powerBound (x y : Λ) (near : dist x y < 1) : dist x y ^ a ≤ dist x y ^ β :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg near.le positiveβ.le lowerβ
  obtain ⟨H, nonnegativeH, estimate⟩ := FiniteAtlasProjectionHolder.bound centers corePatch coreCover F G L fLip gLip
    P A AI D DI (1 / 8) (C ^ 2 * B) (max CF CG) β (by norm_num) (by positivity) positiveβ.le small bunched bounded
    idem inverseF inverseG invariantF invariantG boundF boundIF boundG boundIG
    (by
      intro i hi j hj x hx y hy imageX imageY near
      have actual := holderF ⟨i, hi⟩ ⟨j, hj⟩ x hx y hy imageX imageY
      exact actual.trans ((mul_le_mul_of_nonneg_left (powerBound x y near) nonnegativeCF).trans
        (mul_le_mul_of_nonneg_right (le_max_left CF CG) (Real.rpow_nonneg dist_nonneg _))))
    (by
      intro i hi j hj x hx y hy imageX imageY near
      have actual := holderG ⟨i, hi⟩ ⟨j, hj⟩ x hx y hy imageX imageY
      exact actual.trans ((mul_le_mul_of_nonneg_left (powerBound x y near) nonnegativeCG).trans
        (mul_le_mul_of_nonneg_right (le_max_right CF CG) (Real.rpow_nonneg dist_nonneg _))))
  refine ⟨β, positiveβ, lowerβ.trans_lt smallA, centers, patch, facts, cover, H, nonnegativeH, ?_⟩
  intro i hi x hx y hy source target
  exact estimate i hi ⟨x, hx⟩ source ⟨y, hy⟩ target

end LeanShared.HyperbolicBasicSet
