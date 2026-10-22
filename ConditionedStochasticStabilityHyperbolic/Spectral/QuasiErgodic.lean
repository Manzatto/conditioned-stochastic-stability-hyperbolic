module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CanonicalAverages
public import ConditionedStochasticStabilityHyperbolic.Spectral.MeasurableObservables
public import ConditionedStochasticStabilityHyperbolic.Spectral.Eigenmeasure
public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFeller
public import AbsorbingMarkovChains.QuasiErgodic
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Uniqueness from a basin of conditioned-average convergence

A competing quasi-ergodic measure need only give positive mass to the basin
where the pointwise spectral limit is known. In particular, a continuous
positive eigenfunction at a point of its support suffices. No irreducibility
or aperiodicity assumption is used. These results do not construct spectral
data or establish positivity on the manuscript's basic set.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.QuasiErgodic

open AbsorbingMarkovChains

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [BorelSpace X] (C : CanonicalChain X)

/-- The measurable-observable spectral limit establishes the manuscript's
almost-everywhere QEM property. Smoothing and the measurable left-eigenmeasure
equation are explicit inputs; positivity almost everywhere follows from the
product measure and is not an extra assumption on starting states. -/
theorem eigenvectorMeasure_isQuasiErgodic
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (hP : ∀ (f : X →ᵇ ℝ) (x : X), (P f) x = ∫ y, f y ∂C.killedTransition x)
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ)) (μ : Measure X) [IsFiniteMeasure μ]
    (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y)
    (hsmooth : ∀ h : X → ℝ, Measurable h → (∃ B : ℝ, ∀ y, ‖h y‖ ≤ B) →
      Nonempty (SmoothedObservable C h))
    (hleft : ∀ h : X → ℝ, Measurable h → (∃ B : ℝ, ∀ y, ‖h y‖ ≤ B) →
      (∫ x, ∫ y, h y * d.eigenvector y ∂C.killedTransition x ∂μ) =
        d.rate * ∫ y, h y * d.eigenvector y ∂μ) :
    C.IsQuasiErgodic (LeanShared.eigenvectorMeasure μ d.eigenvector) := by
  refine ⟨eigenvector_product_isProbability d μ hmean hg0, ?_⟩
  intro h hm hb
  have hn : ∃ B : ℝ, ∀ y, ‖h y‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using hb
  obtain ⟨s⟩ := hsmooth h hm hn
  filter_upwards [LeanShared.eigenvectorMeasure_ae_pos μ d.eigenvector
    d.eigenvector.continuous.measurable] with x hx
  have hh := (canonical_measurable_average_limit C hP d μ hmean hg0 s
    (hleft h hm hn) x hx).2
  change Tendsto (fun n : ℕ => ∫ ω, (n : ℝ)⁻¹ *
    ∑ i ∈ Finset.range n, FeynmanKac.ext h (ω i) ∂C.conditionedMeasure x n)
    atTop (𝓝 (∫ y, h y ∂LeanShared.eigenvectorMeasure μ d.eigenvector)) at hh
  have hext : FeynmanKac.ext h = zeroExtension h := by
    funext z
    cases z <;> rfl
  simpa only [pathBirkhoffSum, birkhoffSum, hext] using hh

/-- For finite Borel measures on a metric space, the measurable left equation
is derived from the continuous rank-one gap. Only the smoothing construction
remains an additional input to the abstract QEM existence theorem. -/
theorem eigenvectorMeasure_isQuasiErgodic_of_smoothing
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (hP : ∀ (f : X →ᵇ ℝ) (x : X), (P f) x = ∫ y, f y ∂C.killedTransition x)
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ)) (μ : Measure X) [IsFiniteMeasure μ]
    (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y)
    (hsmooth : ∀ h : X → ℝ, Measurable h → (∃ B : ℝ, ∀ y, ‖h y‖ ≤ B) →
      Nonempty (SmoothedObservable C h)) :
    C.IsQuasiErgodic (LeanShared.eigenvectorMeasure μ d.eigenvector) := by
  have : IsFiniteKernel C.killedTransition :=
    ⟨⟨1, by simp, C.killedTransition_mass_le_one⟩⟩
  apply eigenvectorMeasure_isQuasiErgodic C P hP d μ hmean hg0 hsmooth
  intro h hm hb
  obtain ⟨B, hB⟩ := hb
  have hprod : Integrable (fun y => h y * d.eigenvector y) μ := by
    apply Integrable.of_bound
      (hm.mul d.eigenvector.continuous.measurable).aestronglyMeasurable
      (max B 0 * ‖d.eigenvector‖)
    exact ae_of_all μ fun y => by
      change ‖h y * d.eigenvector y‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul ((hB y).trans (le_max_left _ _))
        (d.eigenvector.norm_coe_le_norm y) (norm_nonneg _)
        (le_max_right _ _)
  exact rankOne_integral_kernel d C.killedTransition hP μ hmean _ hprod

/-- A genuine strong-Feller killed kernel and continuous rank-one spectral
data imply the full bounded-measurable QEM property. Both the smoothing
operators and the measurable left equation have been discharged. -/
theorem eigenvectorMeasure_isQuasiErgodic_of_strongFeller
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (hP : ∀ (f : X →ᵇ ℝ) (x : X), (P f) x = ∫ y, f y ∂C.killedTransition x)
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ)) (μ : Measure X) [IsFiniteMeasure μ]
    (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y) (hSF : HasStrongFellerKernel C) :
    C.IsQuasiErgodic (LeanShared.eigenvectorMeasure μ d.eigenvector) :=
  eigenvectorMeasure_isQuasiErgodic_of_smoothing C P hP d μ hmean hg0
    (exists_smoothedObservable C hSF)

/-- The continuous transfer operator may itself be constructed from the
strong-Feller property. Only existence of its rank-one spectral data and a
nonnegative eigenfunction remain spectral inputs. -/
theorem strongFeller_rankOne_isQuasiErgodic (hSF : HasStrongFellerKernel C)
    (d : RankOneSpectralData (strongFellerTransferOperator C hSF) (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y) :
    C.IsQuasiErgodic (LeanShared.eigenvectorMeasure μ d.eigenvector) :=
  eigenvectorMeasure_isQuasiErgodic_of_strongFeller C _
    (strongFellerTransferOperator_represents C hSF) d μ hmean hg0 hSF

/-- Any quasi-ergodic candidate charging a basin of pointwise conditioned
convergence equals the limiting finite measure. The point selected in the
basin may depend on the observable, which is sufficient for measure equality. -/
theorem eq_of_positive_basin (ν : Measure X) [IsFiniteMeasure ν] (B : Set X)
    (hlim : ∀ (h : X →ᵇ ℝ) (x : X), x ∈ B →
      Tendsto (CanonicalAverages.pathAverage C h x) atTop (𝓝 (∫ y, h y ∂ν)))
    (ν' : Measure X) (hq : C.IsQuasiErgodic ν') (hB : ν' B ≠ 0) :
    ν' = ν := by
  have : IsProbabilityMeasure ν' := hq.1
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro h
  have hb : ∃ b : ℝ, ∀ y, |h y| ≤ b := ⟨‖h‖, fun y => by
    simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm y⟩
  have hae := hq.2 h h.continuous.measurable hb
  obtain ⟨x, hxB, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hB
    (ae_restrict_of_ae hae)
  have hx' : Tendsto (CanonicalAverages.pathAverage C h x) atTop
      (𝓝 (∫ y, h y ∂ν')) := by
    change Tendsto (fun n : ℕ => ∫ ω, (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, FeynmanKac.ext (h : X → ℝ) (ω i)
      ∂C.conditionedMeasure x n) atTop (𝓝 (∫ y, h y ∂ν'))
    have hext : FeynmanKac.ext (h : X → ℝ) = zeroExtension (h : X → ℝ) := by
      funext z
      cases z <;> rfl
    simpa only [pathBirkhoffSum, birkhoffSum, hext] using hx
  exact tendsto_nhds_unique hx' (hlim h x hxB)

omit [BorelSpace X] in
/-- A support point where a continuous function is positive forces the
candidate measure to charge its positive basin. -/
theorem positive_basin_measure_ne_zero (ν : Measure X) (g : X →ᵇ ℝ)
    (p : X) (hp : p ∈ ν.support) (hgp : 0 < g p) :
    ν {x | 0 < g x} ≠ 0 := by
  apply ne_of_gt
  apply (Measure.mem_support_iff_forall p).mp hp
  exact (isOpen_lt continuous_const g.continuous).mem_nhds hgp

/-- The canonical continuous-observable limit already establishes uniqueness among quasi-ergodic
candidates whose support meets the positive eigenfunction basin. Existence still needs the
measurable-observable extension. -/
theorem eq_eigenvectorMeasure_of_support
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (hP : ∀ (f : X →ᵇ ℝ) (x : X), (P f) x = ∫ y, f y ∂C.killedTransition x)
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ)) (μ : Measure X) [IsFiniteMeasure μ]
    (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y)
    (ν' : Measure X) (hq : C.IsQuasiErgodic ν')
    (p : X) (hp : p ∈ ν'.support) (hgp : 0 < d.eigenvector p) :
    ν' = LeanShared.eigenvectorMeasure μ d.eigenvector := by
  let ν := LeanShared.eigenvectorMeasure μ d.eigenvector
  have : IsProbabilityMeasure ν := eigenvector_product_isProbability d μ hmean hg0
  apply eq_of_positive_basin C ν {x | 0 < d.eigenvector x} _ ν' hq
    (positive_basin_measure_ne_zero ν' d.eigenvector p hp hgp)
  intro h x hx
  exact (CanonicalAverages.canonical_conditional_average_limit C P hP d μ hmean hg0
    h x hx).2

/-- Once positivity on a nonempty basic set is available, there is at most
one quasi-ergodic measure whose support contains that set. -/
theorem eq_eigenvectorMeasure_of_basicSet_support
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (hP : ∀ (f : X →ᵇ ℝ) (x : X), (P f) x = ∫ y, f y ∂C.killedTransition x)
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ)) (μ : Measure X) [IsFiniteMeasure μ]
    (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y)
    (Λ : Set X) (hΛ : Λ.Nonempty) (hgΛ : ∀ x ∈ Λ, 0 < d.eigenvector x)
    (ν' : Measure X) (hq : C.IsQuasiErgodic ν') (hsupp : Λ ⊆ ν'.support) :
    ν' = LeanShared.eigenvectorMeasure μ d.eigenvector := by
  obtain ⟨p, hp⟩ := hΛ
  exact eq_eigenvectorMeasure_of_support C P hP d μ hmean hg0 ν' hq p
    (hsupp hp) (hgΛ p hp)

end ConditionedStochasticStabilityHyperbolic.QuasiErgodic
