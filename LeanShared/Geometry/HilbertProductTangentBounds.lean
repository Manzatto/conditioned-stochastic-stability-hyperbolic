module

public import LeanShared.Geometry.HilbertProductTangentEquiv
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The canonical product tangent equivalence is continuous on total spaces.
Its norms are measured with the actual factor and product Riemannian metrics;
no equality between those metrics is asserted. -/

public noncomputable section
open Set IsManifold Bundle Filter
open scoped Manifold ContDiff Topology
namespace LeanShared.HilbertProductDifferential
variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ,E)) ∞ X]
  [TopologicalSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ,F)) ∞ Y]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
local instance boundsOldTangentCharts : ChartedSpace (E × F) (X × Y) := prodChartedSpace E X F Y
local instance boundsNewTangentCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance boundsOldTangentManifold : IsManifold (𝓘(ℝ,E × F)) ∞ (X × Y) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,F)) X Y
local instance boundsNewTangentManifold : IsManifold (𝓘(ℝ,WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]

omit [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem continuous_tangentEquiv : Continuous
    (fun p : TangentBundle (𝓘(ℝ,E)) X × TangentBundle (𝓘(ℝ,F)) Y =>
      (⟨(p.1.proj,p.2.proj), tangentEquiv (E := E) (F := F) (p.1.proj,p.2.proj) (p.1.2,p.2.2)⟩ :
        TangentBundle (𝓘(ℝ,WithLp 2 (E×F))) (X×Y))) := by
  have first := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℝ,E)) (M := X) (I' := 𝓘(ℝ,F)) (M' := Y) (n := 0)).continuous
  have smooth : ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,F)))
      (𝓘(ℝ,WithLp 2 (E×F))) ∞ (@id (X×Y)) := by
    simpa only [modelWithCornersSelf_prod] using
      LinearRechartedManifold.identity_forward (M := X×Y)
        (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F))
  have ready := (smooth.continuous_tangentMap (by simp)).comp first
  convert ready using 1
  funext p
  change (⟨(p.1.proj,p.2.proj), tangentEquiv (E := E) (F := F)
      (p.1.proj,p.2.proj) (p.1.2,p.2.2)⟩ : TangentBundle (𝓘(ℝ,WithLp 2 (E×F))) (X×Y)) =
    ⟨(p.1.proj,p.2.proj), mfderiv ((𝓘(ℝ,E)).prod (𝓘(ℝ,F)))
      (𝓘(ℝ,WithLp 2 (E×F))) (@id (X×Y)) (p.1.proj,p.2.proj) (p.1.2,p.2.2)⟩
  congr 1

omit [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem continuous_tangentEquiv_symm : Continuous
    (fun p : TangentBundle (𝓘(ℝ,WithLp 2 (E×F))) (X×Y) =>
      ((⟨p.proj.1,((tangentEquiv (E := E) (F := F) p.proj).symm p.2).1⟩ : TangentBundle (𝓘(ℝ,E)) X),
       (⟨p.proj.2,((tangentEquiv (E := E) (F := F) p.proj).symm p.2).2⟩ : TangentBundle (𝓘(ℝ,F)) Y))) := by
  have first := (smooth_fst (E := E) (F := F) (X := X) (Y := Y)).continuous_tangentMap
    (by simp)
  have second := (smooth_snd (E := E) (F := F) (X := X) (Y := Y)).continuous_tangentMap
    (by simp)
  simpa only [tangentMap, tangentEquiv_first, tangentEquiv_second] using first.prodMk second

variable
  [IsContinuousRiemannianBundle E (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle F (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [IsContinuousRiemannianBundle (WithLp 2 (E×F))
    (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]

theorem exists_forward_norm_bound (K : Set (X × Y)) (compact : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ‖(tangentEquiv (E := E) (F := F) z).toContinuousLinearMap‖ ≤ C := by
  apply CompactLocalBound.exists_bound compact
  intro z _hz
  let TX := fun x:X=>TangentSpace (𝓘(ℝ,E)) x
  let TY := fun y:Y=>TangentSpace (𝓘(ℝ,F)) y
  let TP := fun p:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) p
  let ex := trivializationAt E TX z.1
  let ey := trivializationAt F TY z.2
  let ep := trivializationAt (WithLp 2 (E×F)) TP z
  let A := fun p:X×Y=>(ep.continuousLinearMapAt ℝ p).comp
    ((tangentEquiv (E := E) (F := F) p).toContinuousLinearMap.comp
      ((ex.symmL ℝ p.1).prodMap (ey.symmL ℝ p.2)))
  let U := (ex.baseSet ×ˢ ey.baseSet) ∩ ep.baseSet
  have openU : IsOpen U := (ex.open_baseSet.prod ey.open_baseSet).inter ep.open_baseSet
  have member : z ∈ U :=
    ⟨⟨FiberBundle.mem_baseSet_trivializationAt' _, FiberBundle.mem_baseSet_trivializationAt' _⟩,
      FiberBundle.mem_baseSet_trivializationAt' _⟩
  have matrix : ContinuousOn A U := by
    apply continuousOn_clm_apply.mpr
    intro v
    have first : ContinuousOn
        (fun p:X×Y=>(⟨p.1, ex.symm p.1 v.1⟩ : TangentBundle (𝓘(ℝ,E)) X))
        (ex.baseSet ×ˢ ey.baseSet) :=
      ex.continuousOn_symm.comp (continuous_fst.prodMk continuous_const).continuousOn
        (fun _ hp=>⟨hp.1,mem_univ _⟩)
    have second : ContinuousOn
        (fun p:X×Y=>(⟨p.2, ey.symm p.2 v.2⟩ : TangentBundle (𝓘(ℝ,F)) Y))
        (ex.baseSet ×ˢ ey.baseSet) :=
      ey.continuousOn_symm.comp (continuous_snd.prodMk continuous_const).continuousOn
        (fun _ hp=>⟨hp.2,mem_univ _⟩)
    have middle := continuous_tangentEquiv.comp_continuousOn (first.prodMk second)
    have coded := ep.continuousOn.comp (middle.mono inter_subset_left)
      (fun p hp=>ep.mem_source.mpr hp.2)
    apply coded.snd.congr
    intro p hp
    change A p v = (ep ⟨p, tangentEquiv (E := E) (F := F) p (ex.symm p.1 v.1,ey.symm p.2 v.2)⟩).2
    change (ep.continuousLinearMapAt ℝ p)
      (tangentEquiv (E := E) (F := F) p (ex.symmL ℝ p.1 v.1, ey.symmL ℝ p.2 v.2)) = _
    rw [ex.symmL_apply hp.1.1, ey.symmL_apply hp.1.2]
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ ep hp.2 _
  have matrixAt : ContinuousAt A z := matrix.continuousAt (openU.mem_nhds member)
  obtain ⟨Cx,posX,boundsX⟩ := CompactRiemannianTrivializations.local_bound (F := E) TX z.1
  obtain ⟨Cy,posY,boundsY⟩ := CompactRiemannianTrivializations.local_bound (F := F) TY z.2
  obtain ⟨Cp,posP,boundsP⟩ := CompactRiemannianTrivializations.local_bound
    (F := WithLp 2 (E×F)) TP z
  have nearX := (continuous_fst.continuousAt (x := z)).tendsto.eventually boundsX
  have nearY := (continuous_snd.continuousAt (x := z)).tendsto.eventually boundsY
  have normAt : ContinuousAt (fun p:X×Y => ‖A p‖) z := by
    exact (continuous_norm (E := E×F →L[ℝ] WithLp 2 (E×F))).continuousAt.comp matrixAt
  have matrixBound : ∀ᶠ p in 𝓝 z, ‖A p‖ < ‖A z‖+1 :=
    normAt.eventually (Iio_mem_nhds (lt_add_one ‖A z‖))
  refine ⟨Cp * ((‖A z‖+1)*(Cx+Cy)), by positivity, ?_⟩
  filter_upwards [nearX.filter_mono nhdsWithin_le_nhds,
    nearY.filter_mono nhdsWithin_le_nhds, boundsP.filter_mono nhdsWithin_le_nhds,
    matrixBound.filter_mono nhdsWithin_le_nhds] with p hx hy hp ha
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let coded := ((ex.continuousLinearMapAt ℝ p.1) v.1,
    (ey.continuousLinearMapAt ℝ p.2) v.2)
  have codeBound : ‖coded‖ ≤ (Cx+Cy)*‖v‖ := by
    rw [Prod.norm_def]
    apply max_le
    · exact ((ex.continuousLinearMapAt ℝ p.1).le_opNorm v.1).trans
        (mul_le_mul (hx.2.1.trans (le_add_of_nonneg_right posY.le))
          (norm_fst_le v) (norm_nonneg _) (by positivity))
    · exact ((ey.continuousLinearMapAt ℝ p.2).le_opNorm v.2).trans
        (mul_le_mul (hy.2.1.trans (le_add_of_nonneg_left posX.le))
          (norm_snd_le v) (norm_nonneg _) (by positivity))
  have reconstruct : tangentEquiv (E := E) (F := F) p v = ep.symmL ℝ p (A p coded) := by
    change tangentEquiv (E := E) (F := F) p v = ep.symmL ℝ p
      (ep.continuousLinearMapAt ℝ p (tangentEquiv (E := E) (F := F) p
        (ex.symmL ℝ p.1 (ex.continuousLinearMapAt ℝ p.1 v.1),
         ey.symmL ℝ p.2 (ey.continuousLinearMapAt ℝ p.2 v.2))))
    rw [ex.symmL_continuousLinearMapAt hx.1, ey.symmL_continuousLinearMapAt hy.1,
      ep.symmL_continuousLinearMapAt hp.1]
  change ‖tangentEquiv (E := E) (F := F) p v‖ ≤ _
  rw [reconstruct]
  calc
    ‖ep.symmL ℝ p (A p coded)‖ ≤ ‖ep.symmL ℝ p‖ * (‖A p‖ * ‖coded‖) :=
      ((ep.symmL ℝ p).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((A p).le_opNorm coded) (norm_nonneg _))
    _ ≤ Cp * ((‖A z‖+1) * ((Cx+Cy)*‖v‖)) :=
      mul_le_mul hp.2.2 (mul_le_mul ha.le codeBound (norm_nonneg _) (by positivity))
        (mul_nonneg (norm_nonneg (A p)) (norm_nonneg coded)) posP.le
    _ = (Cp * ((‖A z‖+1)*(Cx+Cy))) * ‖v‖ := by ring

theorem exists_inverse_norm_bound (K : Set (X × Y)) (compact : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ‖(tangentEquiv (E := E) (F := F) z).symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨Cx,posX,first⟩ := CompactRiemannianCrossMFDeriv.exists_norm_bound
    (@Prod.fst X Y) ((smooth_fst (E := E) (F := F)).of_le (by norm_num)) K compact
  obtain ⟨Cy,posY,second⟩ := CompactRiemannianCrossMFDeriv.exists_norm_bound
    (@Prod.snd X Y) ((smooth_snd (E := E) (F := F)).of_le (by norm_num)) K compact
  refine ⟨Cx+Cy,add_pos posX posY,fun z hz=>?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (add_pos posX posY).le
  intro v
  change ‖(tangentEquiv (E := E) (F := F) z).symm v‖ ≤ _
  rw [Prod.norm_def, tangentEquiv_first, tangentEquiv_second]
  apply max_le
  · exact ((mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,E)) Prod.fst z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((first z hz).trans (le_add_of_nonneg_right posY.le))
        (norm_nonneg _))
  · exact ((mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,F)) Prod.snd z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((second z hz).trans (le_add_of_nonneg_left posX.le))
        (norm_nonneg _))

end LeanShared.HilbertProductDifferential
