module

public import LeanShared.Analysis.ActualFiniteRegularWord

/-!
# Literal real word weights and completed microscopic word estimates

The microscopic chart estimate applies to the chronological nonlinear word
and its accumulated real weight. These are identified with the already
constructed word of completed transfer operators through the faithful
ordinary finite-regular realization. No word realization law is assumed.
-/

@[expose] public noncomputable section

namespace LeanShared.ActualWordMicrolocalBound

open DyadicCompletion FiniteRegularTransferRealization FiniteBlockAnnealedEstimates

variable {X Ω Core V R : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup R] [NormedSpace ℂ R]

/-- Actual real accumulated weight along a chronological nonlinear word. -/
def realWeight (F : Ω → X → X) (g : X → ℝ) : List Ω → X → ℝ
  | [], _ => 1
  | a :: w, x => g x * realWeight F g w (F a x)

theorem realWeight_cast (F : Ω → X → X) (g : X → ℝ) (w : List Ω) (x : X) :
    (realWeight F g w x : ℂ) = ActualFiniteRegularWord.weight F g w x := by
  induction w generalizing x with
  | nil => simp [realWeight, ActualFiniteRegularWord.weight]
  | cons a w ih => simp only [realWeight, Complex.ofReal_mul, ih, ActualFiniteRegularWord.weight]

variable (q : Core →ₗ[ℂ] V) (raw : Core →ₗ[ℂ] (X → ℂ))
  (smooth : Core →ₗ[ℂ] R) (dense : DenseRange smooth)
  (view : R →ₗ[ℂ] (X → ℂ)) (hview : Function.Injective view)
  (hsmooth : ∀ c, view (smooth c) = raw c)
  (realize : R →L[ℂ] closedCore q)
  (hrealize : ∀ c, realize (smooth c) = coreLift q c)
  (F : Ω → X → X) (g : X → ℝ)
  (hregular : ∀ a f, weightedComposition (F a) g (view f) ∈ view.range)
  (hcoreRegular : ∀ a c, weightedComposition (F a) g (raw c) ∈ view.range)
  (C : ℝ)
  (hregularBound : ∀ a f,
    ‖InvariantFiniteRegularTransfer.action view hview F g hregular a f‖ ≤ C * ‖f‖)
  (L : ℝ)
  (hanalyticBound : ∀ a c,
    ‖targetCore q raw R view hview realize F g hcoreRegular a c‖ ≤ L * ‖q c‖)

include hregularBound hsmooth in
/-- Membership of the literal whole-word weighted composition is a
consequence of invariant ordinary regular generators. -/
theorem word_regular (w : List Ω) (c : Core) :
    weightedComposition (ActualFiniteRegularWord.orbit F w) (realWeight F g w) (raw c) ∈ view.range := by
  refine ⟨listWord (InvariantFiniteRegularTransfer.operator view hview F g hregular C hregularBound) w (smooth c), ?_⟩
  funext x
  rw [ActualFiniteRegularWord.regular_word_function view hview F g hregular C hregularBound,
    hsmooth]
  exact congrArg (fun z : ℂ => z * raw c (ActualFiniteRegularWord.orbit F w x))
    (realWeight_cast F g w x).symm

include hregularBound hsmooth in
/-- The ordinary action of the nonlinear whole word is the word of the
constructed ordinary generators, by faithful pointwise representation. -/
theorem whole_action_eq (w : List Ω) (c : Core) :
    regularAction raw R view hview
      (fun _ : Unit => ActualFiniteRegularWord.orbit F w) (realWeight F g w)
      (fun _ => word_regular raw smooth view hview hsmooth F g hregular C hregularBound w) () c =
    listWord (InvariantFiniteRegularTransfer.operator view hview F g hregular C hregularBound) w (smooth c) := by
  apply hview
  funext x
  rw [regularAction_apply]
  rw [ActualFiniteRegularWord.regular_word_function view hview F g hregular C hregularBound,
    hsmooth]
  exact congrArg (fun z : ℂ => z * raw c (ActualFiniteRegularWord.orbit F w x))
    (realWeight_cast F g w x)

include dense hsmooth hrealize hregularBound hanalyticBound in
/-- This is the exact input to the actual manifold chart-pair estimate:
realizing the literal whole-word action equals the completed operator word. -/
theorem realized_whole_action (w : List Ω) (c : Core) :
    realize (regularAction raw R view hview
      (fun _ : Unit => ActualFiniteRegularWord.orbit F w) (realWeight F g w)
      (fun _ => word_regular raw smooth view hview hsmooth F g hregular C hregularBound w) () c) =
    listWord (operator q raw R view hview realize F g hcoreRegular) w (coreLift q c) := by
  rw [whole_action_eq raw smooth view hview hsmooth F g hregular C hregularBound]
  rw [ActualFiniteRegularWord.analytic_word q raw smooth dense view hview hsmooth realize hrealize
    F g hregular hcoreRegular C hregularBound L hanalyticBound, hrealize]

end LeanShared.ActualWordMicrolocalBound
