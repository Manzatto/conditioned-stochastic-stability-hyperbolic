module

public import LeanShared.Dynamics.DynamicalPartition
public import LeanShared.Dynamics.FiniteShannonProduct
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-! Exact additivity of finite-time entropy for independent product
partitions, including zero atoms and zero observation horizon. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {k l : ℕ}

namespace MeasurablePartition

/-- The literal independent product partition, with a finite index. -/
def product (P : MeasurablePartition (X := X) k) (Q : MeasurablePartition (X := Y) l) :
    MeasurablePartition (X := X × Y) (k*l) where
  atom i := P.atom (finProdFinEquiv.symm i).1 ×ˢ Q.atom (finProdFinEquiv.symm i).2
  measurable i := (P.measurable _).prod (Q.measurable _)
  disjoint := by
    intro i j neq
    apply Set.disjoint_left.mpr
    intro z hi hj
    by_cases first : (finProdFinEquiv.symm i).1=(finProdFinEquiv.symm j).1
    · have second : (finProdFinEquiv.symm i).2 ≠ (finProdFinEquiv.symm j).2 := by
        intro eq
        exact neq (finProdFinEquiv.symm.injective (Prod.ext first eq))
      exact (Set.disjoint_left.mp (Q.disjoint second)) hi.2 hj.2
    · exact (Set.disjoint_left.mp (P.disjoint first)) hi.1 hj.1
  covering := by
    apply eq_univ_of_forall
    intro z
    have hp : ∃ i, z.1 ∈ P.atom i := mem_iUnion.mp (P.covering ▸ mem_univ z.1)
    have hq : ∃ j, z.2 ∈ Q.atom j := mem_iUnion.mp (Q.covering ▸ mem_univ z.2)
    obtain ⟨i,hi⟩ := hp
    obtain ⟨j,hj⟩ := hq
    refine mem_iUnion.mpr ⟨finProdFinEquiv (i,j),?_⟩
    simpa only [Equiv.symm_apply_apply] using (show z ∈ P.atom i ×ˢ Q.atom j from ⟨hi,hj⟩)

omit [MeasurableSpace X] [MeasurableSpace Y] in
private theorem iterate_product (T : X → X) (S : Y → Y) (n : ℕ) (z : X × Y) :
    (fun z : X × Y => (T z.1,S z.2))^[n] z=(T^[n] z.1,S^[n] z.2) := by
  induction n with
  | zero => rfl
  | succ n hn => simp only [iterate_succ_apply',hn]

theorem dynamicalAtom_product (P : MeasurablePartition (X := X) k)
    (Q : MeasurablePartition (X := Y) l) (T : X → X) (S : Y → Y)
    (n : ℕ) (word : Fin n → Fin (k*l)) :
    dynamicalAtom (P.product Q) (fun z : X × Y => (T z.1,S z.2)) n word =
      dynamicalAtom P T n (fun i => (finProdFinEquiv.symm (word i)).1) ×ˢ
      dynamicalAtom Q S n (fun i => (finProdFinEquiv.symm (word i)).2) := by
  ext z
  simp only [dynamicalAtom,product,mem_iInter,mem_preimage,mem_prod,iterate_product]
  exact forall_and

private def words (n k l : ℕ) :
    (Fin n → Fin (k*l)) ≃ (Fin n → Fin k) × (Fin n → Fin l) where
  toFun w := (fun i => (finProdFinEquiv.symm (w i)).1,fun i => (finProdFinEquiv.symm (w i)).2)
  invFun w := fun i => finProdFinEquiv (w.1 i,w.2 i)
  left_inv w := by funext i; exact finProdFinEquiv.apply_symm_apply (w i)
  right_inv w := by
    apply Prod.ext <;> funext i <;> simp only [Equiv.symm_apply_apply]

/-- Actual finite-time entropy addition follows from literal product atom
measures, rather than an assumed thermodynamic product theorem. -/
theorem dynamicalEntropy_product (P : MeasurablePartition (X := X) k)
    (Q : MeasurablePartition (X := Y) l) (T : X → X) (S : Y → Y)
    (hT : Measurable T) (hS : Measurable S)
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) :
    dynamicalEntropy (P.product Q) (fun z : X × Y => (T z.1,S z.2)) (μ.prod ν) n =
      dynamicalEntropy P T μ n+dynamicalEntropy Q S ν n := by
  let p := fun w : Fin n → Fin k => μ.real (dynamicalAtom P T n w)
  let q := fun w : Fin n → Fin l => ν.real (dynamicalAtom Q S n w)
  unfold dynamicalEntropy
  simp_rw [dynamicalAtom_product,measureReal_prod_prod]
  change -(∑ w, (p ((words n k l w).1)*q ((words n k l w).2))*
    Real.log (p ((words n k l w).1)*q ((words n k l w).2))) = _
  rw [(words n k l).sum_comp (fun w => (p w.1*q w.2)*Real.log (p w.1*q w.2))]
  rw [Fintype.sum_prod_type]
  exact FiniteShannonProduct.entropy_product p q (P.dynamicalAtoms_total T hT μ n)
    (Q.dynamicalAtoms_total S hS ν n)

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
