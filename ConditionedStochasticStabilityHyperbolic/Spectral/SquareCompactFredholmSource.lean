module

public import LeanShared.Analysis.SquareCompactFredholm
public import ConditionedStochasticStabilityHyperbolic.Spectral.PowerCompactGap
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiverani1999

/-! The square-compact Fredholm source is a proved theorem, rather than a
classical source assumption. It applies to every Banach carrier, including
the physical bounded-continuous-function spaces used by the paper. -/

public section

namespace ConditionedStochasticStabilityHyperbolic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Discharges the universal physical square-compact Fredholm source. -/
theorem PowerCompactGap.squareCompactFredholm : PowerCompactGap.SquareCompactFredholm (F := F) := by
  intro T hT z hz hs
  exact LeanShared.SquareCompactFredholm.eigenvector_of_mem_spectrum T hT hz hs

/-- For a square-compact operator, the residual-spectrum premise in KL follows
without an essential-radius or other spectral background assumption. -/
theorem KellerLiverani1999.noResidualAbove_of_squareCompact
    (T : F →L[ℂ] F) (hT : IsCompactOperator (T ^ 2 : F →L[ℂ] F))
    (α : ℝ) (hα : 0 ≤ α) : KellerLiverani1999.NoResidualAbove T α := by
  intro z hz hinj
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hα.trans_lt hz)
  have hnegative : Function.Injective (T - z • 1 : F →L[ℂ] F) := by
    intro x y hxy
    apply hinj
    have hneg := congrArg Neg.neg hxy
    simpa only [sub_apply, smul_apply, one_apply_eq_self, neg_sub] using hneg
  have surj := LeanShared.SquareCompactFredholm.surjective_shift T hT hz0 hnegative
  have positive : Function.Surjective (z • (1 : F →L[ℂ] F) - T) := by
    intro y
    obtain ⟨x, hx⟩ := surj (-y)
    refine ⟨x, ?_⟩
    have hneg := congrArg Neg.neg hx
    simpa only [sub_apply, smul_apply, one_apply_eq_self, neg_sub, neg_neg] using hneg
  exact positive.denseRange

end ConditionedStochasticStabilityHyperbolic
