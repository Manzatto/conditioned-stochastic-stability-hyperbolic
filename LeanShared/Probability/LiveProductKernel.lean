module

public import LeanShared.Probability.LiveProductMeasure
public import LeanShared.Probability.SubtypeKernel

/-! Independent ambient transitions remain independent on the literal
closed-product live subtype. The auxiliary factor is fully live. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace LeanShared.LiveProductCoordinates
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y]

/-- Exact factorization after pulling back to the closed live state space;
this supplies the independence premise for homeomorphic spectral descent. -/
theorem map_restricted_kernel_product
    (A : Kernel X X) (B : Kernel Y Y) [IsFiniteKernel A] [IsFiniteKernel B]
    (P : Kernel (X × Y) (X × Y))
    (independent : ∀ x y, P (x, y) = (A x).prod (B y))
    (K : Set X) (hK : MeasurableSet K) (z : ↥(K ×ˢ (univ : Set Y))) :
    ((SubtypeKernel.restrict P (K ×ˢ univ) (hK.prod MeasurableSet.univ)) z).map
      (liveProduct K) =
      (SubtypeKernel.restrict A K hK (liveProduct K z).1).prod (B z.val.2) := by
  let : IsFiniteKernel (SubtypeKernel.restrict A K hK) := by
    unfold SubtypeKernel.restrict
    infer_instance
  let : SFinite ((A z.val.1).comap (Subtype.val : K → X)) :=
    inferInstanceAs (SFinite (SubtypeKernel.restrict A K hK (liveProduct K z).1))
  rw [SubtypeKernel.restrict_apply, independent]
  exact map_comap_product K hK (A z.val.1) (B z.val.2)

end LeanShared.LiveProductCoordinates
