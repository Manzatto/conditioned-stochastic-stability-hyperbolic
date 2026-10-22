module

public import LeanShared.Analysis.InvariantFiniteRegularCompatibility
public import LeanShared.Analysis.FiniteBlockAnnealedEstimates

/-!
# Actual completed finite-word transfer and literal manifold composition

Each completed analytic generator is the constructed transfer. Its ordinary little-C^u invariant action is constructed from the same
weighted function. The one-step compatibility proves the corresponding
finite-word compatibility; the regular word represents the actual
accumulated weight and chronological nonlinear map composition. Consequently the finite-word core entering chart microlocal estimates is
exactly the word of the completed operators. No word realization identity
or smooth-core preservation is assumed.
-/

@[expose] public noncomputable section

namespace LeanShared.ActualFiniteRegularWord

open DyadicCompletion FiniteRegularTransferRealization FiniteBlockAnnealedEstimates

variable {X Ω Core V R : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup R] [NormedSpace ℂ R]
  (q : Core →ₗ[ℂ] V) (raw : Core →ₗ[ℂ] (X → ℂ))
  (smooth : Core →ₗ[ℂ] R) (dense : DenseRange smooth)
  (view : R →ₗ[ℂ] (X → ℂ)) (hview : Function.Injective view)
  (hsmooth : ∀ c, view (smooth c) = raw c)
  (realize : R →L[ℂ] closedCore q)
  (hrealize : ∀ c, realize (smooth c) = coreLift q c)
  (F : Ω → X → X) (g : X → ℝ)
  (hregular : ∀ a f, weightedComposition (F a) g (view f) ∈ view.range)
  (hcoreRegular : ∀ a c, weightedComposition (F a) g (raw c) ∈ view.range)

variable (C : ℝ)
  (hregularBound : ∀ a f,
    ‖InvariantFiniteRegularTransfer.action view hview F g hregular a f‖ ≤ C * ‖f‖)
  (L : ℝ)
  (hanalyticBound : ∀ a c,
    ‖targetCore q raw R view hview realize F g hcoreRegular a c‖ ≤ L * ‖q c‖)

/-- Actual nonlinear chronological composition of a finite list. -/
def orbit (F : Ω → X → X) : List Ω → X → X
  | [], x => x
  | a :: w, x => orbit F w (F a x)

/-- The actual signed accumulated weight, before taking absolute values
for the classical principal coefficient. -/
def weight (F : Ω → X → X) (g : X → ℝ) : List Ω → X → ℂ
  | [], _ => 1
  | a :: w, x => (g x : ℂ) * weight F g w (F a x)

theorem regular_word_function (w : List Ω) (f : R) (x : X) :
    view (listWord (InvariantFiniteRegularTransfer.operator view hview F g hregular C hregularBound) w f) x =
      weight F g w x * view f (orbit F w x) := by
  induction w generalizing x with
  | nil => simp only [listWord, one_apply_eq_self, weight, orbit, one_mul]
  | cons a w ih =>
    rw [listWord, ContinuousLinearMap.comp_apply, InvariantFiniteRegularTransfer.operator_function, ih]
    exact (mul_assoc _ _ _).symm

include dense hsmooth hrealize hanalyticBound in
/-- The finite-word completed action is deduced from the actual one-step
construction and ordinary regular-function density. -/
theorem analytic_word (w : List Ω) (f : R) :
    realize (listWord (InvariantFiniteRegularTransfer.operator view hview F g hregular C hregularBound) w f) =
      listWord (operator q raw R view hview realize F g hcoreRegular) w (realize f) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have h := congrArg (fun T : R →L[ℂ] closedCore q =>
      T (listWord (InvariantFiniteRegularTransfer.operator view hview F g hregular C hregularBound) w f))
      (InvariantFiniteRegularCompatibility.analytic_intertwining q raw smooth dense view hview
        hsmooth realize hrealize F g hregular hcoreRegular C hregularBound L hanalyticBound a)
    change realize (InvariantFiniteRegularTransfer.operator view hview F g hregular C hregularBound a
      (listWord (InvariantFiniteRegularTransfer.operator view hview F g hregular C hregularBound) w f)) =
      operator q raw R view hview realize F g hcoreRegular a
        (listWord (operator q raw R view hview realize F g hcoreRegular) w (realize f))
    exact h.trans (congrArg (operator q raw R view hview realize F g hcoreRegular a) ih)

include dense hsmooth hrealize hanalyticBound hregular hregularBound in
/-- Every actual completed word on a smooth input has a constructed
finite-regular output, representing exactly its literal accumulated weight
and nonlinear word. This is the core used by local chart-pair estimates. -/
theorem exists_word_core (w : List Ω) (c : Core) :
    ∃ f : R,
      realize f = listWord (operator q raw R view hview realize F g hcoreRegular) w (coreLift q c) ∧
      ∀ x, view f x = weight F g w x * raw c (orbit F w x) := by
  refine ⟨listWord (InvariantFiniteRegularTransfer.operator view hview F g hregular C hregularBound) w (smooth c), ?_, ?_⟩
  · rw [analytic_word q raw smooth dense view hview hsmooth realize hrealize F g hregular hcoreRegular
      C hregularBound L hanalyticBound, hrealize]
  · intro x
    rw [regular_word_function view hview F g hregular C hregularBound, hsmooth]

end LeanShared.ActualFiniteRegularWord
