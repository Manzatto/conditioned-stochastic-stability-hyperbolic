module

public import LeanShared.Analysis.IntrinsicDistortionRatio
public import LeanShared.Analysis.ActualWordWeightContinuity

/-! The mixed distortion scalar has local continuity from the literal
map/weight continuity and ordinary transported unstable-Jacobian continuity
on the closed cylinder. No continuity of a final supremum is an input. -/

public noncomputable section
open Set
namespace LeanShared.IntrinsicDistortionContinuity
variable {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
  (F : G → X → X) (E : X → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)]
  (D : ∀ a x, E x ≃L[ℝ] E (F a x)) (unstable : ∀ x, Submodule ℝ (E x))

theorem continuousOn_ratio (hF : Continuous (fun z : G × X => F z.1 z.2))
    (g : X → ℝ) (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (ε : ℝ) (hε : 0 < ε)
    (N : ℕ) (U : Set (Fin N → G)) (R : Set ((Fin N → G) × X))
    (hj : ContinuousOn (fun z : (Fin N → G) × X =>
      IntrinsicPrincipalDensity.unstableJacobian F E D (List.ofFn z.1) z.2 (unstable z.2))
      ((U ×ˢ univ) ∩ R)) :
    ContinuousOn (IntrinsicDistortionRatio.ratio F E D unstable g (fun x => g x + ε) N)
      ((U ×ˢ univ) ∩ IntrinsicDistortionRatio.tripleRelation R) := by
  have hw := ActualWordWeightContinuity.continuous_weight F hF g hg N
  have he := ActualWordWeightContinuity.continuous_weight F hF (fun x => g x + ε)
    (hg.add continuous_const) N
  apply IntrinsicDistortionRatio.continuousOn_ratio F E D unstable g (fun x => g x + ε)
    (fun x => add_pos_of_nonneg_of_pos (hg0 x) hε) N
  · exact (hw.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).continuousOn
  · apply hj.comp (continuous_fst.prodMk
      (continuous_snd.comp (continuous_snd.comp continuous_snd))).continuousOn
    intro z hz
    exact ⟨hz.1, hz.2.2.2⟩
  · apply hj.comp (continuous_fst.prodMk
      (continuous_fst.comp (continuous_snd.comp continuous_snd))).continuousOn
    intro z hz
    exact ⟨hz.1, hz.2.2.1⟩
  · exact (he.comp (continuous_fst.prodMk
      (continuous_snd.comp (continuous_snd.comp continuous_snd)))).continuousOn

end LeanShared.IntrinsicDistortionContinuity
