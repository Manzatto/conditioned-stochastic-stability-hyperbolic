module

public import ConditionedStochasticStabilityHyperbolic.Spectral.Eigenmeasure
public import ConditionedStochasticStabilityHyperbolic.Spectral.Normalization
public import LeanShared.Analysis.TriangularPowerBounds
public import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# A dominant rank-one block coupled to nonnilpotent subordinate layers

The subordinate resolvent is constructed from geometric power growth.
Removing the constructed leading projection leaves an actual triangular
operator whose diagonals decay geometrically. Thus arbitrary bounded
couplings preserve a geometric rank-one power gap. No subordinate mixing
or nilpotence hypothesis is required.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace ConditionedStochasticStabilityHyperbolic.Global.DominantBlockGap

open LeanShared.TransientRestriction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Resolvent

variable [CompleteSpace E]

/-- The inverse at the dominant normalized eigenvalue 1. -/
def resolvent (A : E →L[ℝ] E) : E →L[ℝ] E := ∑' n : ℕ, A ^ n

theorem summable_powers (A : E →L[ℝ] E) {C θ : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hbound : ∀ n : ℕ, ‖A ^ n‖ ≤ C * θ ^ n) :
    Summable (fun n : ℕ => A ^ n) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hθ hθ1).mul_left C) hbound

theorem resolvent_mul_one_sub (A : E →L[ℝ] E) {C θ : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hbound : ∀ n : ℕ, ‖A ^ n‖ ≤ C * θ ^ n) :
    resolvent A * (1 - A) = 1 :=
  (summable_powers A hθ hθ1 hbound).tsum_pow_mul_one_sub

theorem one_sub_mul_resolvent (A : E →L[ℝ] E) {C θ : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hbound : ∀ n : ℕ, ‖A ^ n‖ ≤ C * θ ^ n) :
    (1 - A) * resolvent A = 1 :=
  (summable_powers A hθ hθ1 hbound).one_sub_mul_tsum_pow

theorem resolvent_apply_step (A : E →L[ℝ] E) {C θ : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hbound : ∀ n : ℕ, ‖A ^ n‖ ≤ C * θ ^ n) (x : E) :
    resolvent A (A x) + x = resolvent A x := by
  have hh := congrArg (fun T : E →L[ℝ] E => T x)
    (resolvent_mul_one_sub A hθ hθ1 hbound)
  change resolvent A (x - A x) = x at hh
  rw [map_sub] at hh
  exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hh).symm

theorem resolvent_output_step (A : E →L[ℝ] E) {C θ : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hbound : ∀ n : ℕ, ‖A ^ n‖ ≤ C * θ ^ n) (x : E) :
    A (resolvent A x) + x = resolvent A x := by
  have hh := congrArg (fun T : E →L[ℝ] E => T x)
    (one_sub_mul_resolvent A hθ hθ1 hbound)
  change resolvent A x - A (resolvent A x) = x at hh
  exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hh).symm

end Resolvent

/-- A complementary projection has exact positive powers. -/
theorem complement_pow (P R : E →L[ℝ] E)
    (hPR : P * R = R) (hRP : R * P = R) (hRR : R * R = R) (n : ℕ) :
    (P - R) ^ (n + 1) = P ^ (n + 1) - R := by
  have hpow (n : ℕ) : P ^ (n + 1) * R = R := by
    induction n with
    | zero => simpa using hPR
    | succ n ih => rw [pow_succ', mul_assoc, ih, hPR]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, sub_mul, mul_sub, mul_sub, hpow n, hRP, hRR, ← pow_succ]
      noncomm_ring

/-- The normalized leading complementary diagonal has geometric powers,
including the identity at time zero. -/
theorem normalized_complement_bound {D : F →L[ℝ] F} {one : F}
    (d : RankOneSpectralData D one) :
    ∀ n : ℕ, ‖(d.normalizedOperator - d.projection) ^ n‖ ≤
      (‖(1 : F →L[ℝ] F)‖ + d.errorConstant) * d.decay ^ n := by
  have hPR : d.normalizedOperator * d.projection = d.projection := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [mul_apply_eq_comp, RankOneSpectralData.projection,
      ContinuousLinearMap.smulRight_apply, map_smul, d.normalized_eigenvector]
  have hRR : d.projection * d.projection = d.projection := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [mul_apply_eq_comp, RankOneSpectralData.projection,
      ContinuousLinearMap.smulRight_apply, map_smul, d.mean_eigenvector,
      one_smul]
  intro n
  cases n with
  | zero => simp; exact d.errorConstant_nonneg
  | succ n =>
      rw [complement_pow d.normalizedOperator d.projection hPR
        d.projection_mul_normalizedOperator hRR n]
      exact (d.power_gap (n + 1)).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (norm_nonneg _)) (pow_nonneg d.decay_nonneg _))

section SubordinateDominant

variable [CompleteSpace E]
  (A : E →L[ℝ] E) (B : E →L[ℝ] F) {D : F →L[ℝ] F} {oneF : F}
  (d : RankOneSpectralData D oneF)

/-- The dominant block's left functional includes all weighted first
entrance contributions from the subordinate lower level. -/
def lowerMean : E →L[ℝ] ℝ := d.mean.comp (B.comp (resolvent A))

def assembledMean : (E × F) →L[ℝ] ℝ :=
  (lowerMean A B d).comp (ContinuousLinearMap.fst ℝ E F) +
    d.mean.comp (ContinuousLinearMap.snd ℝ E F)

def assembledVector : E × F := (0, d.eigenvector)

def assembledProjection : (E × F) →L[ℝ] (E × F) :=
  (assembledMean A B d).smulRight (assembledVector (E := E) d)

omit [CompleteSpace E] in
theorem assembled_mean_vector : assembledMean A B d (assembledVector (E := E) d) = 1 := by
  simp [assembledMean, assembledVector, lowerMean, d.mean_eigenvector]

omit [CompleteSpace E] in
theorem assembled_right_eigen :
    block A B d.normalizedOperator (assembledVector (E := E) d) = assembledVector (E := E) d := by
  simp [block_apply, assembledVector, d.normalized_eigenvector]

theorem assembled_left_eigen {C θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hbound : ∀ n : ℕ, ‖A ^ n‖ ≤ C * θ ^ n) (f : E × F) :
    assembledMean A B d (block A B d.normalizedOperator f) = assembledMean A B d f := by
  have hstep := congrArg (fun x => d.mean (B x)) (resolvent_apply_step A hθ hθ1 hbound f.1)
  simp only [map_add] at hstep
  change d.mean (B (resolvent A (A f.1))) +
      d.mean (B f.1 + d.normalizedOperator f.2) =
    d.mean (B (resolvent A f.1)) + d.mean f.2
  rw [map_add, d.mean_normalizedOperator]
  rw [← add_assoc, hstep]

omit [CompleteSpace E] in
/-- Subtracting the actual rank-one projection leaves a triangular
operator with both diagonal growth rates below one. -/
theorem complement_eq_block :
    block A B d.normalizedOperator - assembledProjection A B d =
      block A (B - (lowerMean A B d).smulRight d.eigenvector)
        (d.normalizedOperator - d.projection) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext
  · change A x - assembledMean A B d (x, y) • (0 : E) = A x
    simp
  · change B x + d.normalizedOperator y -
      (lowerMean A B d x + d.mean y) • d.eigenvector =
        (B x - lowerMean A B d x • d.eigenvector) +
          (d.normalizedOperator y - d.mean y • d.eigenvector)
    rw [add_smul]
    abel

/-- A dominant normalized local rank-one gap and arbitrary nonnilpotent
subordinate geometric growth produce a constructed global block gap. -/
theorem assembled_power_gap {CA θ η : ℝ} (hCA : 0 ≤ CA) (hθ : 0 ≤ θ)
    (hθη : θ < η) (hdη : d.decay < η) (hη1 : η < 1)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * θ ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖block A B d.normalizedOperator ^ n - assembledProjection A B d‖ ≤ K * η ^ n := by
  let β := (max θ d.decay + η) / 2
  have hmax : max θ d.decay < η := max_lt hθη hdη
  have hβη : β < η := by dsimp [β]; linarith
  have hθβ : θ < β := by dsimp [β]; linarith [le_max_left θ d.decay]
  have hdβ : d.decay < β := by dsimp [β]; linarith [le_max_right θ d.decay]
  have hβ : 0 < β := hθ.trans_lt hθβ
  have hθ1 : θ < 1 := hθη.trans hη1
  let P := block A B d.normalizedOperator
  let R := assembledProjection A B d
  have hPR : P * R = R := by
    apply ContinuousLinearMap.ext
    intro f
    change P ((assembledMean A B d f) • assembledVector (E := E) d) =
      assembledMean A B d f • assembledVector (E := E) d
    rw [map_smul, assembled_right_eigen]
  have hRP : R * P = R := by
    apply ContinuousLinearMap.ext
    intro f
    change assembledMean A B d (P f) • assembledVector (E := E) d =
      assembledMean A B d f • assembledVector (E := E) d
    rw [assembled_left_eigen A B d hθ hθ1 hA]
  have hRR : R * R = R := by
    apply ContinuousLinearMap.ext
    intro f
    change assembledMean A B d (assembledMean A B d f • assembledVector (E := E) d) •
        assembledVector (E := E) d = assembledMean A B d f • assembledVector (E := E) d
    rw [map_smul, assembled_mean_vector, smul_eq_mul, mul_one]
  obtain ⟨K, hK, hbound⟩ := LeanShared.TriangularPowerBounds.exists_geometric_block_bound
    A (B - (lowerMean A B d).smulRight d.eigenvector) (d.normalizedOperator - d.projection)
    hCA (add_nonneg (norm_nonneg _) d.errorConstant_nonneg) hβ hβη
    (fun n => (hA n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hθ hθβ.le n) hCA))
    (fun n => (normalized_complement_bound d n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ d.decay_nonneg hdβ.le n)
      (add_nonneg (norm_nonneg _) d.errorConstant_nonneg)))
  refine ⟨K + ‖(1 : (E × F) →L[ℝ] (E × F)) - R‖,
    add_nonneg hK (norm_nonneg _), ?_⟩
  intro n
  cases n with
  | zero =>
      simp only [pow_zero, mul_one]
      exact le_add_of_nonneg_left hK
  | succ n =>
      change ‖P ^ (n + 1) - R‖ ≤ _
      rw [← complement_pow P R hPR hRP hRR n]
      change ‖(block A B d.normalizedOperator - assembledProjection A B d) ^ (n + 1)‖ ≤ _
      rw [complement_eq_block A B d]
      exact (hbound (n + 1)).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (norm_nonneg _)) (pow_nonneg (hθ.trans_lt hθη).le _))

/-- Constructed leading spectral data after attaching a subordinate lower
level. The distinguished observation is the dominant diagonal's original
observation, extended by zero to the subordinate coordinate. -/
def assembledData {CA θ : ℝ} (hCA : 0 ≤ CA) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * θ ^ n) :
    RankOneSpectralData (block A B d.normalizedOperator) ((0 : E), oneF) := by
  let η := (max θ d.decay + 1) / 2
  have hmax : max θ d.decay < 1 := max_lt hθ1 d.decay_lt_one
  have hθη : θ < η := by dsimp [η]; linarith [le_max_left θ d.decay]
  have hdη : d.decay < η := by dsimp [η]; linarith [le_max_right θ d.decay]
  have hη1 : η < 1 := by dsimp [η]; linarith
  let hg := assembled_power_gap A B d hCA hθ hθη hdη hη1 hA
  exact {
    rate := 1
    rate_pos := zero_lt_one
    mean := assembledMean A B d
    eigenvector := assembledVector (E := E) d
    mean_eigenvector := assembled_mean_vector A B d
    mean_one_pos := by simpa [assembledMean] using d.mean_one_pos
    right_eigenvector := by simpa using assembled_right_eigen A B d
    errorConstant := Classical.choose hg
    errorConstant_nonneg := (Classical.choose_spec hg).1
    decay := η
    decay_nonneg := (hθ.trans_lt hθη).le
    decay_lt_one := hη1
    power_gap := by simpa [assembledProjection] using (Classical.choose_spec hg).2 }

end SubordinateDominant

section DominantSubordinate

variable [CompleteSpace F]
  (A : F →L[ℝ] F) (B : E →L[ℝ] F) {D : E →L[ℝ] E} {oneE : E}
  (d : RankOneSpectralData D oneE)

/-- The dominant eigenfunction is lifted through all future residence in
an upper subordinate layer. -/
def upperVector : E × F := (d.eigenvector, resolvent A (B d.eigenvector))

def upperMean : (E × F) →L[ℝ] ℝ := d.mean.comp (ContinuousLinearMap.fst ℝ E F)

def upperProjection : (E × F) →L[ℝ] (E × F) :=
  (upperMean (F := F) d).smulRight (upperVector A B d)

omit [CompleteSpace F] in
theorem upper_mean_vector : upperMean (F := F) d (upperVector A B d) = 1 := d.mean_eigenvector

theorem upper_right_eigen {C θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hbound : ∀ n : ℕ, ‖A ^ n‖ ≤ C * θ ^ n) :
    block d.normalizedOperator B A (upperVector A B d) = upperVector A B d := by
  apply Prod.ext
  · exact d.normalized_eigenvector
  · change B d.eigenvector + A (resolvent A (B d.eigenvector)) = resolvent A (B d.eigenvector)
    exact (add_comm _ _).trans (resolvent_output_step A hθ hθ1 hbound _)

omit [CompleteSpace F] in
theorem upper_left_eigen (f : E × F) :
    upperMean (F := F) d (block d.normalizedOperator B A f) = upperMean (F := F) d f :=
  d.mean_normalizedOperator f.1

omit [CompleteSpace F] in
theorem upper_complement_eq_block :
    block d.normalizedOperator B A - upperProjection A B d =
      block (d.normalizedOperator - d.projection)
        (B - d.mean.smulRight (resolvent A (B d.eigenvector))) A := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext
  · rfl
  · change B x + A y - d.mean x • resolvent A (B d.eigenvector) =
      (B x - d.mean x • resolvent A (B d.eigenvector)) + A y
    abel

/-- Adding an upper subordinate layer preserves a constructed rank-one
power gap, without nilpotence or subordinate mixing. -/
theorem upper_power_gap {CA θ η : ℝ} (hCA : 0 ≤ CA) (hθ : 0 ≤ θ)
    (hθη : θ < η) (hdη : d.decay < η) (hη1 : η < 1)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * θ ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖block d.normalizedOperator B A ^ n - upperProjection A B d‖ ≤ K * η ^ n := by
  let β := (max θ d.decay + η) / 2
  have hmax : max θ d.decay < η := max_lt hθη hdη
  have hβη : β < η := by dsimp [β]; linarith
  have hθβ : θ < β := by dsimp [β]; linarith [le_max_left θ d.decay]
  have hdβ : d.decay < β := by dsimp [β]; linarith [le_max_right θ d.decay]
  have hβ : 0 < β := hθ.trans_lt hθβ
  have hθ1 : θ < 1 := hθη.trans hη1
  let P := block d.normalizedOperator B A
  let R := upperProjection A B d
  have hPR : P * R = R := by
    apply ContinuousLinearMap.ext
    intro f
    change P (upperMean (F := F) d f • upperVector A B d) =
      upperMean (F := F) d f • upperVector A B d
    rw [map_smul, upper_right_eigen A B d hθ hθ1 hA]
  have hRP : R * P = R := by
    apply ContinuousLinearMap.ext
    intro f
    change upperMean (F := F) d (P f) • upperVector A B d =
      upperMean (F := F) d f • upperVector A B d
    rw [upper_left_eigen A B d]
  have hRR : R * R = R := by
    apply ContinuousLinearMap.ext
    intro f
    change upperMean (F := F) d (upperMean (F := F) d f • upperVector A B d) • upperVector A B d =
      upperMean (F := F) d f • upperVector A B d
    rw [map_smul, upper_mean_vector, smul_eq_mul, mul_one]
  obtain ⟨K, hK, hbound⟩ := LeanShared.TriangularPowerBounds.exists_geometric_block_bound
    (d.normalizedOperator - d.projection)
    (B - d.mean.smulRight (resolvent A (B d.eigenvector))) A
    (add_nonneg (norm_nonneg _) d.errorConstant_nonneg) hCA hβ hβη
    (fun n => (normalized_complement_bound d n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ d.decay_nonneg hdβ.le n)
      (add_nonneg (norm_nonneg _) d.errorConstant_nonneg)))
    (fun n => (hA n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hθ hθβ.le n) hCA))
  refine ⟨K + ‖(1 : (E × F) →L[ℝ] (E × F)) - R‖,
    add_nonneg hK (norm_nonneg _), ?_⟩
  intro n
  cases n with
  | zero =>
      simp only [pow_zero, mul_one]
      exact le_add_of_nonneg_left hK
  | succ n =>
      change ‖P ^ (n + 1) - R‖ ≤ _
      rw [← complement_pow P R hPR hRP hRR n]
      change ‖(block d.normalizedOperator B A - upperProjection A B d) ^ (n + 1)‖ ≤ _
      rw [upper_complement_eq_block A B d]
      exact (hbound (n + 1)).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (norm_nonneg _)) (pow_nonneg (hθ.trans_lt hθη).le _))

/-- Constructed leading data after attaching an upper subordinate level.
The distinguished observation remains the local dominant observation. -/
def upperData {CA θ : ℝ} (hCA : 0 ≤ CA) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * θ ^ n) :
    RankOneSpectralData (block d.normalizedOperator B A) (oneE, (0 : F)) := by
  let η := (max θ d.decay + 1) / 2
  have hmax : max θ d.decay < 1 := max_lt hθ1 d.decay_lt_one
  have hθη : θ < η := by dsimp [η]; linarith [le_max_left θ d.decay]
  have hdη : d.decay < η := by dsimp [η]; linarith [le_max_right θ d.decay]
  have hη1 : η < 1 := by dsimp [η]; linarith
  let hg := upper_power_gap A B d hCA hθ hθη hdη hη1 hA
  exact {
    rate := 1
    rate_pos := zero_lt_one
    mean := upperMean (F := F) d
    eigenvector := upperVector A B d
    mean_eigenvector := upper_mean_vector A B d
    mean_one_pos := d.mean_one_pos
    right_eigenvector := by simpa using upper_right_eigen A B d hθ hθ1 hA
    errorConstant := Classical.choose hg
    errorConstant_nonneg := (Classical.choose_spec hg).1
    decay := η
    decay_nonneg := (hθ.trans_lt hθη).le
    decay_lt_one := hη1
    power_gap := by simpa [upperProjection] using (Classical.choose_spec hg).2 }

end DominantSubordinate

section RawRates

/-- Normalize subordinate growth by the dominant rate, without requiring
that either raw rate lie below one. -/
theorem normalized_growth_bound (A : E →L[ℝ] E) {C β r : ℝ}
    (_hβ : 0 ≤ β) (hr : 0 < r) (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ C * β ^ n) :
    ∀ n : ℕ, ‖(r⁻¹ • A) ^ n‖ ≤ C * (β / r) ^ n := by
  intro n
  calc
    _ = (r⁻¹) ^ n * ‖A ^ n‖ := by
      rw [smul_pow, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) n)]
    _ ≤ (r⁻¹) ^ n * (C * β ^ n) :=
      mul_le_mul_of_nonneg_left (hA n) (pow_nonneg (inv_nonneg.mpr hr.le) n)
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

/-- Scalar normalization respects the actual three triangular blocks. -/
theorem rescale_normalized_block (A : E →L[ℝ] E) (B : E →L[ℝ] F) (D : F →L[ℝ] F)
    {r : ℝ} (hr : 0 < r) :
    r • block (r⁻¹ • A) (r⁻¹ • B) (r⁻¹ • D) = block A B D := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, y⟩
  change (r • (r⁻¹ • A x), r • (r⁻¹ • B x + r⁻¹ • D y)) = (A x, B x + D y)
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

/-- Raw-rate leading data after adjoining an actual subordinate lower
operator with growth strictly below the dominant leading eigenvalue. -/
def ofSubordinateLower [CompleteSpace E]
    (A : E →L[ℝ] E) (B : E →L[ℝ] F) {D : F →L[ℝ] F} {oneF : F}
    (d : RankOneSpectralData D oneF) {CA β : ℝ}
    (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * β ^ n) :
    RankOneSpectralData (block A B D) ((0 : E), oneF) := by
  let dn := assembledData (d.rate⁻¹ • A) (d.rate⁻¹ • B) d hCA
    (div_nonneg hβ d.rate_pos.le) ((div_lt_one d.rate_pos).mpr hβr)
    (normalized_growth_bound A hβ d.rate_pos hA)
  have he : d.rate • block (d.rate⁻¹ • A) (d.rate⁻¹ • B) d.normalizedOperator = block A B D :=
    rescale_normalized_block A B D d.rate_pos
  exact he ▸ dn.rescale d.rate d.rate_pos

/-- Raw-rate leading data after adjoining an actual subordinate upper
operator. No nilpotence, mixing or raw rate less than one is assumed. -/
def ofSubordinateUpper [CompleteSpace F]
    (A : F →L[ℝ] F) (B : E →L[ℝ] F) {D : E →L[ℝ] E} {oneE : E}
    (d : RankOneSpectralData D oneE) {CA β : ℝ}
    (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * β ^ n) :
    RankOneSpectralData (block D B A) (oneE, (0 : F)) := by
  let dn := upperData (d.rate⁻¹ • A) (d.rate⁻¹ • B) d hCA
    (div_nonneg hβ d.rate_pos.le) ((div_lt_one d.rate_pos).mpr hβr)
    (normalized_growth_bound A hβ d.rate_pos hA)
  have he : d.rate • block d.normalizedOperator (d.rate⁻¹ • B) (d.rate⁻¹ • A) = block D B A :=
    rescale_normalized_block D B A d.rate_pos
  exact he ▸ dn.rescale d.rate d.rate_pos

private theorem transported_rate {P Q : E →L[ℝ] E} {one : E}
    (h : P = Q) (d : RankOneSpectralData P one) : (h ▸ d).rate = d.rate := by
  cases h
  rfl

/-- Adjoining a subordinate lower aggregate preserves the dominant rate. -/
theorem ofSubordinateLower_rate [CompleteSpace E]
    (A : E →L[ℝ] E) (B : E →L[ℝ] F) {D : F →L[ℝ] F} {oneF : F}
    (d : RankOneSpectralData D oneF) {CA β : ℝ}
    (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * β ^ n) :
    (ofSubordinateLower A B d hCA hβ hβr hA).rate = d.rate := by
  dsimp only [ofSubordinateLower, RankOneSpectralData.normalizedOperator]
  rw [transported_rate]
  change d.rate * 1 = d.rate
  exact mul_one _

/-- Adjoining a subordinate upper aggregate preserves the dominant rate. -/
theorem ofSubordinateUpper_rate [CompleteSpace F]
    (A : F →L[ℝ] F) (B : E →L[ℝ] F) {D : E →L[ℝ] E} {oneE : E}
    (d : RankOneSpectralData D oneE) {CA β : ℝ}
    (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * β ^ n) :
    (ofSubordinateUpper A B d hCA hβ hβr hA).rate = d.rate := by
  dsimp only [ofSubordinateUpper, RankOneSpectralData.normalizedOperator]
  rw [transported_rate]
  change d.rate * 1 = d.rate
  exact mul_one _

end RawRates

end ConditionedStochasticStabilityHyperbolic.Global.DominantBlockGap
