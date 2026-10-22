module
public import LeanShared.Analysis.FiniteBlockAnnealedEstimates

/-! Literal chronological weighted words with a separate spatial label at
each departure and a terminal function. The empty word keeps its terminal
function. This algebra lets fixed finite families of genuine weighted
operators produce cutoff products without any smoothness claim for the
accumulated finite-regular amplitude. -/
@[expose] public noncomputable section
namespace LeanShared.ActualFiniteLabelledWord
open FiniteBlockAnnealedEstimates
variable {X Ω I H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def amplitude (F : Ω → X → X) (weight : I → X → ℂ)
    (terminal : X → ℂ) : List (Ω × I) → X → ℂ
  | [], x => terminal x
  | a :: word, x => weight a.2 x * amplitude F weight terminal word (F a.1 x)

theorem physical_word (F : Ω → X → X) (weight : I → X → ℂ)
    (view : H → X → ℂ) (A : Ω × I → H →L[ℂ] H)
    (action : ∀ a v x, view (A a v) x = weight a.2 x * view v (F a.1 x))
    (v : H) (word : List (Ω × I)) (x : X) :
    view (listWord A word v) x = amplitude F weight (view v) word x := by
  induction word generalizing x with
  | nil => rfl
  | cons a word ih =>
    rw [listWord, ContinuousLinearMap.comp_apply, action, ih]
    rfl

end LeanShared.ActualFiniteLabelledWord
