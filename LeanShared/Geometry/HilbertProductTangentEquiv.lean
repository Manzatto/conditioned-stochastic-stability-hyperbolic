module

public import LeanShared.Geometry.CompactRiemannianCrossMFDeriv
public import LeanShared.Geometry.LinearRechartedDifferential
public import LeanShared.Geometry.HilbertProductDifferential
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The canonical product tangent equivalence is derived from the actual
smooth identity recharting. It respects arbitrary Riemannian norms. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HilbertProductDifferential
variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace F Y]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
local instance oldTangentCharts : ChartedSpace (E × F) (X × Y) := prodChartedSpace E X F Y
local instance newTangentCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
variable [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]

@[expose] def tangentEquiv (z:X×Y) :
    (TangentSpace (𝓘(ℝ,E)) z.1 × TangentSpace (𝓘(ℝ,F)) z.2) ≃L[ℝ]
      TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z :=
  (LinearRechartedManifold.identityDifferential (M:=X×Y)
    (LinearRechartedManifold.hilbertProductEquiv (A:=E) (B:=F)) z).toLinearEquiv.toContinuousLinearEquiv

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
private theorem first_backward (z:X×Y) :
    (mfderiv (𝓘(ℝ,E×F)) (𝓘(ℝ,E)) Prod.fst z).comp
      (mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,E×F)) (@id (X×Y)) z) =
      mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,E)) Prod.fst z := by
  have first : MDifferentiable (𝓘(ℝ,E×F)) (𝓘(ℝ,E)) (@Prod.fst X Y) := by
    simpa only [modelWithCornersSelf_prod] using
      (mdifferentiable_fst : MDifferentiable ((𝓘(ℝ,E)).prod (𝓘(ℝ,F))) (𝓘(ℝ,E)) (@Prod.fst X Y))
  have back := (LinearRechartedManifold.identity_backward (M:=X×Y)
    (LinearRechartedManifold.hilbertProductEquiv (A:=E) (B:=F))).mdifferentiable (by simp)
  exact (mfderiv_comp z (first z) (back z)).symm

omit [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem tangentEquiv_first (z:X×Y)
    (v:TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z) :
    ((tangentEquiv z).symm v).1 =
      mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,E)) Prod.fst z v := by
  have eq := congrArg (fun A=>A v) (first_backward z)
  have coded (w:TangentSpace (𝓘(ℝ,E×F)) z) :
      mfderiv (𝓘(ℝ,E×F)) (𝓘(ℝ,E)) Prod.fst z w = w.1 := by
    rw [modelWithCornersSelf_prod,mfderiv_fst]
    rfl
  change (mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,E×F)) (@id (X×Y)) z v).1 = _
  exact (coded _).symm.trans eq

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
private theorem second_backward (z:X×Y) :
    (mfderiv (𝓘(ℝ,E×F)) (𝓘(ℝ,F)) Prod.snd z).comp
      (mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,E×F)) (@id (X×Y)) z) =
      mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,F)) Prod.snd z := by
  have first : MDifferentiable (𝓘(ℝ,E×F)) (𝓘(ℝ,F)) (@Prod.snd X Y) := by
    simpa only [modelWithCornersSelf_prod] using
      (mdifferentiable_snd : MDifferentiable ((𝓘(ℝ,E)).prod (𝓘(ℝ,F))) (𝓘(ℝ,F)) (@Prod.snd X Y))
  have back := (LinearRechartedManifold.identity_backward (M:=X×Y)
    (LinearRechartedManifold.hilbertProductEquiv (A:=E) (B:=F))).mdifferentiable (by simp)
  exact (mfderiv_comp z (first z) (back z)).symm

omit [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem tangentEquiv_second (z:X×Y)
    (v:TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z) :
    ((tangentEquiv z).symm v).2 =
      mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,F)) Prod.snd z v := by
  have eq := congrArg (fun A=>A v) (second_backward z)
  have coded (w:TangentSpace (𝓘(ℝ,E×F)) z) :
      mfderiv (𝓘(ℝ,E×F)) (𝓘(ℝ,F)) Prod.snd z w = w.2 := by
    rw [modelWithCornersSelf_prod,mfderiv_snd]
    rfl
  change (mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,E×F)) (@id (X×Y)) z v).2 = _
  exact (coded _).symm.trans eq

end LeanShared.HilbertProductDifferential
