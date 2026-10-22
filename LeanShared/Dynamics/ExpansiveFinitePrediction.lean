module

public import LeanShared.Dynamics.FiniteMapPartition
public import LeanShared.Dynamics.CompactPartitionApproximation
public import LeanShared.Dynamics.FiniteExpansiveCylinders

/-! Every finite measurable partition is approximable in probability by
an actual finite window of a small-mesh expansive itinerary. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
namespace MeasurablePartition

@[expose] def finiteName {k : ℕ} (P : MeasurablePartition (X := X) k) (T : X ≃ₜ X)
    (N : ℕ) (x : X) : (Fin (N+1) → Fin k) × (Fin (N+1) → Fin k) :=
  ⟨fun n => P.label ((T : X → X)^[n.val] x), fun n => P.label ((T.symm : X → X)^[n.val] x)⟩

omit [CompactSpace X] in
theorem finiteName_measurable {k : ℕ} (P : MeasurablePartition (X := X) k) (T : X ≃ₜ X)
    (N : ℕ) : Measurable (P.finiteName T N) := by
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr (fun n => P.label_measurable.comp (T.continuous.measurable.iterate n.val))
  · exact measurable_pi_iff.mpr (fun n => P.label_measurable.comp (T.symm.continuous.measurable.iterate n.val))

/-- This is the approximation part of the finite-generator theorem,
proved from compact regularity and expansivity rather than assumed. -/
theorem exists_finite_prediction {k l : ℕ} (P : MeasurablePartition (X := X) k)
    (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (mesh : ∀ i x y, x ∈ P.atom i → y ∈ P.atom i → dist x y ≤ c)
    (Q : MeasurablePartition (X := X) l) (μ : ProbabilityMeasure X)
    (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∃ prediction : ((Fin (N+1) → Fin k) × (Fin (N+1) → Fin k)) → Fin l,
      (μ : Measure X).real {x | Q.label x ≠ prediction (P.finiteName T N x)} < ε := by
  obtain ⟨δ,positiveδ,predict⟩ := Q.exists_prediction_scale μ ε positive
  obtain ⟨N,_,detect⟩ := LeanShared.FiniteExpansiveCylinders.exists_finite_separation T
    (isCompact_univ : IsCompact (univ : Set X)) c (fun x _ y _ => expansive x y) δ positiveδ
  let R := of_finite_map (P.finiteName T N) (P.finiteName_measurable T N)
  have meshR (i) (x y : X) (hx : x ∈ R.atom i) (hy : y ∈ R.atom i) : dist x y < δ := by
    have equal : P.finiteName T N x=P.finiteName T N y := hx.trans hy.symm
    apply detect x y
    intro n hn
    have future := congrFun (congrArg Prod.fst equal) ⟨n,by omega⟩
    have past := congrFun (congrArg Prod.snd equal) ⟨n,by omega⟩
    exact ⟨mem_univ _,mem_univ _,mesh _ _ _ (P.label_mem _) ((P.label_eq_iff _ _).mp future.symm),
      mem_univ _,mem_univ _,mesh _ _ _ (P.label_mem _) ((P.label_eq_iff _ _).mp past.symm)⟩
  obtain ⟨prediction,error⟩ := predict _ R meshR
  refine ⟨N,prediction ∘ (Fintype.equivFin _),?_⟩
  simpa only [R,of_finite_map_label,Function.comp_apply] using error

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
