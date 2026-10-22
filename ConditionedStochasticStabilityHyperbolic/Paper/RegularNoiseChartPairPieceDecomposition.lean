module
public import LeanShared.Geometry.ChartPairTransfer
public import LeanShared.Geometry.FiniteCaptureWordCutoffs
public import LeanShared.Geometry.ChartLocalization
import Mathlib.Algebra.BigOperators.Fin

/-! The literal chart-pair transfer of a word is the finite sum of its
localized pieces: one pressure-centre cutoff at the source point, the full
beta word whose first label is the output chart, and one auxiliary terminal
cutoff at the endpoint. The terminal cutoff multiplies an input that is
already localized in the input chart, so it is inserted without changing
the action; no terminal partition function is duplicated. -/
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BigOperators
attribute [local instance] Classical.propDecidable
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared

variable {E P M I Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [TopologicalSpace M] [ChartedSpace E M]
  [Fintype I] [Fintype Y]

theorem wordCutoff_cons {K : Set M} {v : I → Set M}
    (d : FiniteSmoothCapturePartition.Data (E := E) K v) {N : ℕ}
    (points : Fin (N+1) → M) (i : I) (labels : Fin N → I) :
    FiniteSmoothCapturePartition.wordCutoff d points (Fin.cons i labels) =
      d.beta i (points 0) *
        FiniteSmoothCapturePartition.wordCutoff d (fun k => points k.succ) labels := by
  unfold FiniteSmoothCapturePartition.wordCutoff
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Pointwise piece decomposition of one chart-pair transfer. -/
theorem chart_pair_piece_decomposition
    {K : Set M} {v : I → Set M} (d : FiniteSmoothCapturePartition.Data (E := E) K v)
    {Kp : Set M} {vp : Y → Set M} (p : FiniteSmoothCapturePartition.Data (E := E) Kp vp)
    (out inp : OpenPartialHomeomorph M P) (i : I)
    {N : ℕ} (points : M → Fin (N+1) → M) (start : ∀ m, points m 0 = m)
    (F : M → M)
    (g : M → ℝ) (τ : M → ℂ) (u : P → ℂ)
    (terminal : ∀ x ∈ inp.source, u (inp x) ≠ 0 → τ x = 1)
    (capture : ∀ m, d.beta i m * g m ≠ 0 →
      m ∈ p.capture ∧ ∀ k : Fin N, points m k.succ ∈ d.capture) (z : P) :
    ChartPairTransfer.pair out inp (fun m => (d.beta i m : ℂ)) F g u z =
      ∑ y : Y, ∑ labels : Fin N → I,
        ChartLocalization.coordinate out
          (fun m => (p.beta y m : ℂ) *
            (FiniteSmoothCapturePartition.wordCutoff d (points m) (Fin.cons i labels) : ℂ))
          (fun m => (g m : ℂ) * τ (F m)) z *
        (if F (out.symm z) ∈ inp.source then u (inp (F (out.symm z))) else 0) := by
  classical
  by_cases target : z ∈ out.target
  · let m := out.symm z
    let input : ℂ := if F m ∈ inp.source then u (inp (F m)) else 0
    have pairValue : ChartPairTransfer.pair out inp (fun m => (d.beta i m : ℂ)) F g u z =
        (d.beta i m : ℂ) * (g m : ℂ) * input := by
      simp only [ChartPairTransfer.pair, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left target]
      rfl
    have pieceValue (y : Y) (labels : Fin N → I) :
        ChartLocalization.coordinate out
          (fun m => (p.beta y m : ℂ) *
            (FiniteSmoothCapturePartition.wordCutoff d (points m) (Fin.cons i labels) : ℂ))
          (fun m => (g m : ℂ) * τ (F m)) z * input =
        ((p.beta y m : ℂ) *
          (FiniteSmoothCapturePartition.wordCutoff d (fun k => points m k.succ) labels : ℂ)) *
          ((d.beta i m : ℂ) * (g m : ℂ) * (τ (F m) * input)) := by
      simp only [ChartLocalization.coordinate, ite_eq_left target]
      change ((p.beta y m : ℂ) *
        (FiniteSmoothCapturePartition.wordCutoff d (points m) (Fin.cons i labels) : ℂ)) *
          ((g m : ℂ) * τ (F m)) * input = _
      rw [wordCutoff_cons d (points m) i labels, start m]
      push_cast
      ring
    have terminalValue : τ (F m) * input = input := by
      by_cases source : F m ∈ inp.source
      · by_cases zero : u (inp (F m)) = 0
        · simp only [input, ite_eq_left source, zero, mul_zero]
        · simp only [input, ite_eq_left source, terminal (F m) source zero, one_mul]
      · simp only [input, ite_eq_right source, mul_zero]
    rw [pairValue]
    change _ = ∑ y : Y, ∑ labels : Fin N → I,
      ChartLocalization.coordinate out
        (fun m => (p.beta y m : ℂ) *
          (FiniteSmoothCapturePartition.wordCutoff d (points m) (Fin.cons i labels) : ℂ))
        (fun m => (g m : ℂ) * τ (F m)) z * input
    simp_rw [pieceValue, terminalValue]
    by_cases zero : d.beta i m * g m = 0
    · have zeroC : (d.beta i m : ℂ) * (g m : ℂ) = 0 := by
        rw [← Complex.ofReal_mul, zero, Complex.ofReal_zero]
      simp only [zeroC, zero_mul, mul_zero, Finset.sum_const_zero]
    · obtain ⟨sourceCapture, captured⟩ := capture m zero
      have pressureSum : (∑ y : Y, (p.beta y m : ℂ)) = 1 := by
        have real := p.one m sourceCapture
        rw [← Complex.ofReal_sum, real, Complex.ofReal_one]
      have wordSum : (∑ labels : Fin N → I,
          (FiniteSmoothCapturePartition.wordCutoff d (fun k => points m k.succ) labels : ℂ)) = 1 := by
        have real := FiniteSmoothCapturePartition.wordCutoff_sum d
          (fun k : Fin N => points m k.succ) captured
        rw [← Complex.ofReal_sum]
        convert congrArg (fun x : ℝ => (x : ℂ)) real using 2
        congr 1
        ext label
        simp only [Finset.mem_univ]
      calc (d.beta i m : ℂ) * (g m : ℂ) * input
          = (∑ y : Y, (p.beta y m : ℂ)) * (∑ labels : Fin N → I,
              (FiniteSmoothCapturePartition.wordCutoff d (fun k => points m k.succ) labels : ℂ)) *
              ((d.beta i m : ℂ) * (g m : ℂ) * input) := by
            rw [pressureSum, wordSum]; ring
        _ = _ := by
            rw [Finset.sum_mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun y _ => ?_)
            rw [Finset.sum_mul]
  · have pairZero : ChartPairTransfer.pair out inp (fun m => (d.beta i m : ℂ)) F g u z = 0 := by
      simp only [ChartPairTransfer.pair, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right target]
    rw [pairZero]
    symm
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro labels _
    simp only [ChartLocalization.coordinate, ite_eq_right target, zero_mul]

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
