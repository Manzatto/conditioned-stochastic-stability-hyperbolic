module

public import LeanShared.Dynamics.BlockRelationExpansivity
import all LeanShared.Dynamics.ClosedRelationFiniteDetection
import all LeanShared.Dynamics.BlockRelationExpansivity
public import LeanShared.Dynamics.ExpansiveFinitePrediction

/-! A partition whose atoms control a full consecutive n-step word
predicts every finite measurable partition from a finite T^n-name. The
uniform finite detector is derived from the original expansivity radius. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions.MeasurablePartition
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exists_block_finite_prediction {k l : ℕ} (P : MeasurablePartition (X := X) k)
    (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (n : ℕ) (positiveN : 0 < n)
    (mesh : ∀ i x y, x ∈ P.atom i → y ∈ P.atom i →
      ∀ j < n, dist (T^[j] x) (T^[j] y) ≤ c)
    (Q : MeasurablePartition (X := X) l) (μ : ProbabilityMeasure X)
    (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∃ prediction : ((Fin (N+1) → Fin k) × (Fin (N+1) → Fin k)) → Fin l,
      (μ : Measure X).real {x | Q.label x ≠ prediction (P.finiteName (T^n) N x)} < ε := by
  obtain ⟨δ, positiveδ, predict⟩ := Q.exists_prediction_scale μ ε positive
  obtain ⟨N, _, detect⟩ := ClosedRelationFiniteDetection.exists_finite_detection (T^n)
    (BlockRelationExpansivity.relation T c n) (BlockRelationExpansivity.relation_closed T c n)
    (BlockRelationExpansivity.separates T c expansive n positiveN) δ positiveδ
  let R := of_finite_map (P.finiteName (T^n) N) (P.finiteName_measurable (T^n) N)
  have meshR (i) (x y : X) (hx : x ∈ R.atom i) (hy : y ∈ R.atom i) : dist x y < δ := by
    have equal : P.finiteName (T^n) N x = P.finiteName (T^n) N y := hx.trans hy.symm
    apply detect x y
    unfold ClosedRelationFiniteDetection.window
    intro j hj
    have future := congrFun (congrArg Prod.fst equal) ⟨j, by omega⟩
    have past := congrFun (congrArg Prod.snd equal) ⟨j, by omega⟩
    exact ⟨mesh _ _ _ (P.label_mem _) ((P.label_eq_iff _ _).mp future.symm),
      mesh _ _ _ (P.label_mem _) ((P.label_eq_iff _ _).mp past.symm)⟩
  obtain ⟨prediction, error⟩ := predict _ R meshR
  refine ⟨N, prediction ∘ (Fintype.equivFin _), ?_⟩
  simpa only [R, of_finite_map_label, Function.comp_apply] using error

end LeanShared.ThermodynamicDefinitions.MeasurablePartition
