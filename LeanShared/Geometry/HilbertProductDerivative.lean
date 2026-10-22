module
public import LeanShared.Geometry.HilbertProductTangentEquiv
public import LeanShared.Dynamics.ProductIsolationMixing
public import LeanShared.Geometry.DiffeomorphismIterates

/-! The actual derivative of a product is conjugate to the two factor
derivatives, before any product hyperbolic certificate is constructed. -/
public noncomputable section
open Set Function IsManifold Bundle
open scoped Manifold ContDiff Topology
namespace LeanShared.HilbertProductDifferential
variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ,E)) ∞ X]
  [TopologicalSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ,F)) ∞ Y]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
local instance derivativeOldCharts : ChartedSpace (E × F) (X × Y) := prodChartedSpace E X F Y
local instance derivativeNewCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance derivativeOldManifold : IsManifold (𝓘(ℝ,E × F)) ∞ (X × Y) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,F)) X Y
local instance derivativeNewManifold : IsManifold (𝓘(ℝ,WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ,E)) ∞ X] [IsManifold (𝓘(ℝ,F)) ∞ Y]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem mdifferentiable_prodMap (T : X → X) (S : Y → Y)
    (forwardT : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (forwardS : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S) :
    MDifferentiable (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,WithLp 2 (E×F))) (Prod.map T S) := by
  have ordinary : MDifferentiable (𝓘(ℝ,E×F)) (𝓘(ℝ,E×F)) (Prod.map T S) := by
    simpa only [modelWithCornersSelf_prod] using forwardT.prodMap forwardS
  have front := (LinearRechartedManifold.identity_forward (M := X×Y)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F))).mdifferentiable (by simp)
  have back := (LinearRechartedManifold.identity_backward (M := X×Y)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F))).mdifferentiable (by simp)
  exact front.comp (ordinary.comp back)

omit [IsManifold (𝓘(ℝ,E)) ∞ X] [IsManifold (𝓘(ℝ,F)) ∞ Y]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem derivative_prodMap (T : X → X) (S : Y → Y)
    (forwardT : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (forwardS : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S)
    (z : X × Y) (v : TangentSpace (𝓘(ℝ,E)) z.1 × TangentSpace (𝓘(ℝ,F)) z.2) :
    mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,WithLp 2 (E×F))) (Prod.map T S) z
      (tangentEquiv z v) =
    tangentEquiv (T z.1,S z.2)
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T z.1 v.1,
       mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) S z.2 v.2) := by
  have forwardProduct := mdifferentiable_prodMap T S forwardT forwardS
  apply (tangentEquiv (E := E) (F := F) (T z.1,S z.2)).symm.injective
  apply Prod.ext
  · rw [ContinuousLinearEquiv.symm_apply_apply]
    have same := congrArg (fun A => A (tangentEquiv z v))
      (fst_intertwines T S forwardT forwardProduct z)
    rw [tangentEquiv_first]
    calc
      _ = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T z.1
        (mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,E)) Prod.fst z (tangentEquiv z v)) := same
      _ = _ := by rw [← tangentEquiv_first, ContinuousLinearEquiv.symm_apply_apply]
  · rw [ContinuousLinearEquiv.symm_apply_apply]
    have same := congrArg (fun A => A (tangentEquiv z v))
      (snd_intertwines T S forwardS forwardProduct z)
    rw [tangentEquiv_second]
    calc
      _ = mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) S z.2
        (mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,F)) Prod.snd z (tangentEquiv z v)) := same
      _ = _ := by rw [← tangentEquiv_second, ContinuousLinearEquiv.symm_apply_apply]

omit [IsManifold (𝓘(ℝ,E)) ∞ X] [IsManifold (𝓘(ℝ,F)) ∞ Y]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem derivative_iterate_prodMap (T : X → X) (S : Y → Y)
    (forwardT : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (forwardS : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S)
    (n : ℕ) (z : X × Y)
    (v : TangentSpace (𝓘(ℝ,E)) z.1 × TangentSpace (𝓘(ℝ,F)) z.2) :
    mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,WithLp 2 (E×F))) ((Prod.map T S)^[n]) z
      (tangentEquiv z v) =
    tangentEquiv (T^[n] z.1,S^[n] z.2)
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (T^[n]) z.1 v.1,
       mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) (S^[n]) z.2 v.2) := by
  have same : (Prod.map T S)^[n] = Prod.map (T^[n]) (S^[n]) := funext (iterate_independent T S n)
  rw [same]
  exact derivative_prodMap (T^[n]) (S^[n])
    (DiffeomorphismIterates.mdifferentiable_iterate T forwardT n)
    (DiffeomorphismIterates.mdifferentiable_iterate S forwardS n) z v

end LeanShared.HilbertProductDifferential
