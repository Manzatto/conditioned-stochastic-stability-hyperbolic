module

public import LeanShared.Dynamics.DynamicalPartition
public import LeanShared.Dynamics.FinitePartitionEntropy
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Analysis.Subadditive

/-! Subadditivity of the literal finite-time Shannon entropy of an
invariant probability measure. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}

private def appendEquiv (n m : ℕ) :
    ((Fin n → Fin k) × (Fin m → Fin k)) ≃ (Fin (n+m) → Fin k) where
  toFun p := Fin.addCases p.1 p.2
  invFun w := ⟨fun j => w (Fin.castAdd m j),fun j => w (Fin.natAdd n j)⟩
  left_inv p := by ext j <;> simp
  right_inv w := by
    funext j
    exact Fin.addCases (fun _ => by simp) (fun _ => by simp) j

private theorem atom_append (P : MeasurablePartition (X := X) k) (T : X → X)
    (n m : ℕ) (p : (Fin n → Fin k) × (Fin m → Fin k)) :
    dynamicalAtom P T (n+m) (appendEquiv n m p) =
      dynamicalAtom P T n p.1 ∩ (T^[n]) ⁻¹' dynamicalAtom P T m p.2 := by
  ext x
  constructor
  · intro hx
    constructor
    · apply mem_iInter.mpr
      intro j
      simpa only [appendEquiv,Equiv.coe_fn_mk,Fin.addCases_left,Fin.val_castAdd] using
        mem_iInter.mp hx (Fin.castAdd m j)
    · apply mem_iInter.mpr
      intro j
      have h := mem_iInter.mp hx (Fin.natAdd n j)
      simpa only [appendEquiv,Equiv.coe_fn_mk,Fin.addCases_right,Fin.val_natAdd,
        Nat.add_comm n j.val,iterate_add_apply,mem_preimage] using h
  · rintro ⟨hx,hy⟩
    apply mem_iInter.mpr
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [appendEquiv,Equiv.coe_fn_mk,Fin.addCases_left,Fin.val_castAdd] using mem_iInter.mp hx i
    · simpa only [appendEquiv,Equiv.coe_fn_mk,Fin.addCases_right,Fin.val_natAdd,
        Nat.add_comm n i.val,iterate_add_apply,mem_preimage] using mem_iInter.mp hy i

/-- The actual word entropies are subadditive. Invariance is the only
dynamical hypothesis; no entropy-limit or partition theorem is assumed. -/
theorem MeasurablePartition.dynamicalEntropy_subadditive (P : MeasurablePartition (X := X) k)
    (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ]
    (invariant : MeasurePreserving T μ μ) : Subadditive (dynamicalEntropy P T μ) := by
  intro n m
  let A := dynamicalAtom P T n
  let B := fun w => (T^[n]) ⁻¹' dynamicalAtom P T m w
  have measurableA := P.dynamicalAtom_measurable T invariant.measurable n
  have measurableB := fun w => (P.dynamicalAtom_measurable T invariant.measurable m w).preimage
    (invariant.measurable.iterate n)
  have disjointB : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j different
    exact (P.dynamicalAtoms_disjoint T m different).preimage _
  have coverB : ⋃ w, B w=univ := by
    rw [←preimage_iUnion,P.dynamicalAtoms_cover T m,preimage_univ]
  have bound := FinitePartitionEntropy.refinement_le μ A B measurableA measurableB
    (P.dynamicalAtoms_disjoint T n) disjointB (P.dynamicalAtoms_cover T n) coverB
  have joint : dynamicalEntropy P T μ (n+m) =
      -(∑ i, ∑ j, μ.real (A i ∩ B j)*Real.log (μ.real (A i ∩ B j))) := by
    unfold dynamicalEntropy
    rw [←(appendEquiv (k := k) n m).sum_comp]
    simp only [atom_append,Fintype.sum_prod_type,A,B]
  rw [joint]
  have masses (w : Fin m → Fin k) : μ.real (B w)=μ.real (dynamicalAtom P T m w) :=
    (invariant.iterate n).measureReal_preimage
      (P.dynamicalAtom_measurable T invariant.measurable m w).nullMeasurableSet
  simpa only [masses,A,dynamicalEntropy,sub_eq_add_neg] using bound

end LeanShared.ThermodynamicDefinitions
