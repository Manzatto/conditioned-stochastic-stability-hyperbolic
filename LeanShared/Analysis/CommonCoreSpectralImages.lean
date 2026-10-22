module
public import LeanShared.Analysis.SquareCompactTwoNormBounds
public import LeanShared.Analysis.CompactTwoNormRieszRange
public import LeanShared.Analysis.MeromorphicCommonResolvent
public import LeanShared.Analysis.CommonAmbientContour
public import LeanShared.Analysis.CommonCoreFiniteImages
import Mathlib.Tactic.Linarith

/-! The actual stable generalized eigenspaces have the same common ambient
image. All finite-dimensional projectors and meromorphic data are derived
from compactness, power estimates and the dense common core. -/
public noncomputable section
open Set Metric
namespace LeanShared.CommonCoreSpectralImages
variable {E F Z W Reg : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem exists_stable_images (P : E →L[ℂ] E) (Q : F →L[ℂ] F) (L : Z →L[ℂ] Z)
    (a : E →L[ℂ] Z) (b : F →L[ℂ] Z)
    (actionA : a.comp P = L.comp a) (actionB : b.comp Q = L.comp b)
    (cA : Reg → E) (cF : Reg → F) (denseA : DenseRange cA) (denseF : DenseRange cF)
    (common : ∀ v, a (cA v) = b (cF v))
    (i : E →L[ℂ] W) (compactI : IsCompactOperator i)
    (α R C D : ℝ) (hα : 0 < α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(P^n) x‖ ≤ C*α^n*‖x‖+D*R^n*‖i x‖)
    (compactQ : IsCompactOperator (Q^2 : F →L[ℂ] F)) (z : ℂ) (hz : α < ‖z‖) :
    ∃ n m : ℕ,
      (∀ k, ((P-z•1)^(n+k)).ker = ((P-z•1)^n).ker) ∧
      (∀ k, ((Q-z•1)^(m+k)).ker = ((Q-z•1)^m).ker) ∧
      ((P-z•1)^n).ker.map a.toLinearMap = ((Q-z•1)^m).ker.map b.toLinearMap := by
  obtain ⟨Rq,Cq,hRq,hCq,boundsQ⟩ := SquareCompactTwoNormBounds.bounds Q α hα
  have estimateQ : ∀ n x, ‖(Q^n) x‖ ≤ Cq*α^n*‖x‖+1*Rq^n*‖(Q^2) x‖ := by
    intro n x
    simpa only [one_mul] using boundsQ n x
  obtain ⟨n,rP,positiveP,finiteP,stableP,contoursP⟩ :=
    CompactTwoNormRieszRange.exists_contours P i compactI α R C D hα.le hR hC hD estimate z hz
  obtain ⟨m,rQ,positiveQ,finiteQ,stableQ,contoursQ⟩ :=
    CompactTwoNormRieszRange.exists_contours Q (Q^2) compactQ α Rq Cq 1 hα.le hRq hCq zero_le_one estimateQ z hz
  let t := min rP (min rQ (‖z‖-α))
  let ε := t/2
  have positiveT : 0 < t := lt_min positiveP (lt_min positiveQ (sub_pos.mpr hz))
  have positiveε : 0 < ε := half_pos positiveT
  have lessP : ε < rP := (half_lt_self positiveT).trans_le (min_le_left _ _)
  have lessQ : ε < rQ := (half_lt_self positiveT).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have lessGap : ε < ‖z‖-α := (half_lt_self positiveT).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have outside : ∀ w ∈ sphere z ε, α < ‖w‖ := by
    intro w hw
    have distance : ‖z-w‖ = ε := by simpa only [mem_sphere,dist_eq_norm,norm_sub_rev] using hw
    have triangle := norm_sub_norm_le z w
    linarith
  have cp := contoursP ε positiveε lessP
  have cq := contoursQ ε positiveε lessQ
  let pp := RieszContourIdempotent.projector P z ε
  let pq := RieszContourIdempotent.projector Q z ε
  let : FiniteDimensional ℂ pp.toLinearMap.range := by rw [show pp.range = _ from cp.2]; exact finiteP
  let : FiniteDimensional ℂ pq.toLinearMap.range := by rw [show pq.range = _ from cq.2]; exact finiteQ
  have meromorphicP := CompactTwoNormMeromorphicResolvent.meromorphicOn P i compactI α R C D hα.le hR hC hD estimate
  have meromorphicQ := SquareCompactTwoNormBounds.meromorphicOn Q compactQ α hα
  have matchProjectors (v : Reg) : a (pp (cA v)) = b (pq (cF v)) := by
    apply CommonAmbientContour.projector_match P Q a b (cA v) (cF v) z ε positiveε.le cp.1 cq.1
    intro w hw
    exact MeromorphicCommonResolvent.eq P Q L a b actionA actionB (cA v) (cF v) (common v)
      α hα.le meromorphicP meromorphicQ w (outside w hw) (cp.1 hw) (cq.1 hw)
  have images := CommonCoreFiniteImages.map_range_eq pp pq a b cA cF denseA denseF matchProjectors
  refine ⟨n,m,stableP,stableQ,?_⟩
  change pp.range.map a.toLinearMap = pq.range.map b.toLinearMap at images
  rwa [cp.2,cq.2] at images
end LeanShared.CommonCoreSpectralImages
