module
public import LeanShared.Geometry.HilbertProductTangentBounds
public import LeanShared.Geometry.HilbertProductDerivative
public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Analysis.IntertwinedProjectionSubspaces
public import Mathlib.LinearAlgebra.Projection

/-! The actual product stable/unstable splitting and continuous projection
are constructed from the two factor hyperbolic certificates. -/
public noncomputable section
open Set Function IsManifold Bundle
open scoped Manifold ContDiff Topology
namespace LeanShared.HyperbolicBasicSet.HilbertProduct
open HilbertProductDifferential
variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ,E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ,F)) ∞ Y]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
local instance productOldCharts : ChartedSpace (E × F) (X × Y) := prodChartedSpace E X F Y
local instance productNewCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance productNewManifold : IsManifold (𝓘(ℝ,WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} {K : Set X} {L : Set Y}
  (a : HyperbolicData (E := E) T K) (b : HyperbolicData (E := F) S L)

@[expose] def stable (z:X×Y) : Submodule ℝ (TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z) :=
  ((a.stable z.1).prod (b.stable z.2)).map (tangentEquiv z).toLinearMap

@[expose] def unstable (z:X×Y) : Submodule ℝ (TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z) :=
  ((a.unstable z.1).prod (b.unstable z.2)).map (tangentEquiv z).toLinearMap

@[expose] def projection (z:X×Y) :
    TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z →L[ℝ] TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z :=
  (tangentEquiv z).toContinuousLinearMap.comp
    (((a.projection z.1).prodMap (b.projection z.2)).comp
      (tangentEquiv z).symm.toContinuousLinearMap)

omit [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem projection_apply (z:X×Y) (v:TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z) :
    projection a b z v = tangentEquiv z
      (a.projection z.1 ((tangentEquiv z).symm v).1,
       b.projection z.2 ((tangentEquiv z).symm v).2) := rfl

theorem projection_range (z:X×Y) (hz:z∈K×ˢL) :
    (projection a b z).range = stable a b z := by
  have equal := IntertwinedProjectionSubspaces.range_map
    ((a.projection z.1).prodMap (b.projection z.2)) (projection a b z) (tangentEquiv z)
    (fun v=>by simp only [projection_apply, ContinuousLinearEquiv.symm_apply_apply]; rfl)
  rw [← equal]
  change ((a.projection z.1).toLinearMap.prodMap (b.projection z.2).toLinearMap).range.map _ = _
  rw [LinearMap.range_prodMap]
  rw [a.projection_range z.1 hz.1,b.projection_range z.2 hz.2]
  rfl

theorem projection_kernel (z:X×Y) (hz:z∈K×ˢL) :
    (projection a b z).ker = unstable a b z := by
  have equal := IntertwinedProjectionSubspaces.kernel_map
    ((a.projection z.1).prodMap (b.projection z.2)) (projection a b z) (tangentEquiv z)
    (fun v=>by simp only [projection_apply, ContinuousLinearEquiv.symm_apply_apply]; rfl)
  rw [← equal]
  change ((a.projection z.1).toLinearMap.prodMap (b.projection z.2).toLinearMap).ker.map _ = _
  rw [LinearMap.ker_prodMap]
  rw [a.projection_kernel z.1 hz.1,b.projection_kernel z.2 hz.2]
  rfl

omit [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem projection_idempotent (z:X×Y) (hz:z∈K×ˢL) :
    (projection a b z).comp (projection a b z) = projection a b z := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, projection_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  congr 1
  apply Prod.ext
  · exact congrArg (fun P=>P ((tangentEquiv z).symm v).1) (a.projection_idempotent z.1 hz.1)
  · exact congrArg (fun P=>P ((tangentEquiv z).symm v).2) (b.projection_idempotent z.2 hz.2)

theorem complementary (z:X×Y) (hz:z∈K×ˢL) : IsCompl (stable a b z) (unstable a b z) := by
  rw [← projection_range a b z hz, ← projection_kernel a b z hz]
  apply LinearMap.IsIdempotentElem.isCompl
  ext v
  exact congrArg (fun P=>P v) (projection_idempotent a b z hz)

omit [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem continuous_splitting : ContinuousOn
    (fun v : TangentBundle (𝓘(ℝ,WithLp 2 (E×F))) (X×Y) =>
      (⟨v.proj, projection a b v.proj v.2⟩ : TangentBundle (𝓘(ℝ,WithLp 2 (E×F))) (X×Y)))
    {v | v.proj∈K×ˢL} := by
  have first := a.continuous_splitting.comp
    ((smooth_fst (E := E) (F := F) (X := X) (Y := Y)).continuous_tangentMap (by simp)).continuousOn
    (fun (v:TangentBundle (𝓘(ℝ,WithLp 2 (E×F))) (X×Y)) (hz:v.proj∈K×ˢL)=>hz.1)
  have second := b.continuous_splitting.comp
    ((smooth_snd (E := E) (F := F) (X := X) (Y := Y)).continuous_tangentMap (by simp)).continuousOn
    (fun (v:TangentBundle (𝓘(ℝ,WithLp 2 (E×F))) (X×Y)) (hz:v.proj∈K×ˢL)=>hz.2)
  have ready := continuous_tangentEquiv.comp_continuousOn (first.prodMk second)
  apply ready.congr
  intro v _hv
  simp only [Function.comp_apply, tangentMap, projection_apply,
    tangentEquiv_first, tangentEquiv_second]
  rfl

omit a b [IsManifold (𝓘(ℝ,E)) ∞ X] [IsManifold (𝓘(ℝ,F)) ∞ Y]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem derivative_map_product (forwardT : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (forwardS : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S) (z:X×Y)
    (U : Submodule ℝ (TangentSpace (𝓘(ℝ,E)) z.1))
    (V : Submodule ℝ (TangentSpace (𝓘(ℝ,F)) z.2)) :
    ((U.prod V).map (tangentEquiv z).toLinearMap).map
      (mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,WithLp 2 (E×F))) (T.prodCongr S) z).toLinearMap =
    ((U.map (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T z.1).toLinearMap).prod
      (V.map (mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) S z.2).toLinearMap)).map
      (tangentEquiv (T z.1,S z.2)).toLinearMap := by
  have intertwines :
      (mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,WithLp 2 (E×F))) (T.prodCongr S) z).toLinearMap.comp
        (tangentEquiv z).toLinearMap =
      (tangentEquiv (T z.1,S z.2)).toLinearMap.comp
        ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T z.1).toLinearMap.prodMap
          (mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) S z.2).toLinearMap) := by
    apply LinearMap.ext
    intro v
    exact derivative_prodMap T S forwardT forwardS z v
  rw [← Submodule.map_comp,intertwines]
  erw [Submodule.map_comp,LinearMap.prodMap_map_prod]
  rfl

omit [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem stable_invariant (forwardT : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (forwardS : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S) (z:X×Y) (hz:z∈K×ˢL) :
    (stable a b z).map
      (mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,WithLp 2 (E×F))) (T.prodCongr S) z).toLinearMap =
      stable a b ((T.prodCongr S) z) := by
  unfold stable
  rw [derivative_map_product forwardT forwardS z,
    a.stable_invariant z.1 hz.1,b.stable_invariant z.2 hz.2]
  rfl

omit [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem unstable_invariant (forwardT : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (forwardS : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S) (z:X×Y) (hz:z∈K×ˢL) :
    (unstable a b z).map
      (mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,WithLp 2 (E×F))) (T.prodCongr S) z).toLinearMap =
      unstable a b ((T.prodCongr S) z) := by
  unfold unstable
  rw [derivative_map_product forwardT forwardS z,
    a.unstable_invariant z.1 hz.1,b.unstable_invariant z.2 hz.2]
  rfl

end LeanShared.HyperbolicBasicSet.HilbertProduct
