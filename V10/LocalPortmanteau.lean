import V10.ContinuousMeasureTests
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Local continuity sets from genuine compact-test convergence

A smooth cutoff equal to one on the closure of the counted set converts local
convergence into weak convergence of finite positive measures. Probability
normalization supplies the finite-measure continuity-set theorem, including a
separate zero-limit case. The cutoff is constructed, not assumed.
-/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal ContDiff
namespace V10.LocalPortmanteau

/-- Portmanteau for finite positive measures, including a zero limiting measure. -/
theorem finiteMeasure_tendsto_null_frontier
    {ι : Type*} {l : Filter ι} {μ : ι → FiniteMeasure ℂ} {ν : FiniteMeasure ℂ}
    (ht : Tendsto μ l (𝓝 ν)) {A : Set ℂ} (hA : ν (frontier A) = 0) :
    Tendsto (fun i => μ i A) l (𝓝 (ν A)) := by
  by_cases hn : ν = 0
  · subst ν
    have hm : Tendsto (fun i => (μ i).mass) l (𝓝 (0 : ℝ≥0)) := by simpa using ht.mass
    simpa using tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
      (fun i => (show (0 : ℝ≥0) ≤ μ i A from bot_le))
      (fun i => (μ i).apply_le_mass A)
  · have hf : ν.normalize (frontier A) = 0 := by
      rw [ν.normalize_eq_of_nonzero hn, hA, mul_zero]
    have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      (ν.tendsto_normalize_of_tendsto ht hn) hf
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using ht.mass.mul hp

/-- Multiplying a locally finite measure by a nonnegative continuous compact
cutoff gives a genuine finite measure. -/
theorem finite_withDensity {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψn : ∀ z, 0 ≤ ψ z) :
    IsFiniteMeasure (μ.withDensity (fun z => ENNReal.ofReal (ψ z))) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (hψ.integrable_of_hasCompactSupport hψc)
    (ae_of_all _ hψn)]
  exact ENNReal.ofReal_ne_top

/-- Exact compact-cutoff identity for test integrals. -/
theorem integral_withDensity_cutoff (μ : Measure ℂ) {ψ : ℂ → ℝ}
    (hψ : Continuous ψ) (hψn : ∀ z, 0 ≤ ψ z) (f : ℂ → ℝ) :
    (∫ z, f z ∂μ.withDensity (fun z => ENNReal.ofReal (ψ z))) =
      ∫ z, ψ z * f z ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun z => ENNReal.ofReal (ψ z))
    (ENNReal.continuous_ofReal.measurable.comp hψ.measurable)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hψn _), smul_eq_mul]

/-- A cutoff equal to one on the set leaves its actual measure unchanged. -/
theorem withDensity_cutoff_apply (μ : Measure ℂ) {ψ : ℂ → ℝ} {A : Set ℂ}
    (hA : MeasurableSet A) (hψ1 : ∀ z ∈ A, ψ z = 1) :
    μ.withDensity (fun z => ENNReal.ofReal (ψ z)) A = μ A := by
  rw [withDensity_apply _ hA]
  calc
    _ = ∫⁻ z in A, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_congr_ae
      exact ae_restrict_of_forall_mem hA (fun z hz => by simp only [hψ1 z hz, ENNReal.ofReal_one])
    _ = μ A := by simp

/-- Local Portmanteau: all continuous compact tests in U imply convergence
on every relatively compact measurable continuity set in U. -/
theorem tendsto_measure_of_continuous_compact_tests
    {ι : Type*} {l : Filter ι} {μ : ι → Measure ℂ} {ν : Measure ℂ}
    [∀ i, IsFiniteMeasureOnCompacts (μ i)] [IsFiniteMeasureOnCompacts ν]
    {U : Set ℂ} (hU : IsOpen U)
    (htest : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      Tendsto (fun i => ∫ z, f z ∂μ i) l (𝓝 (∫ z, f z ∂ν)))
    {A : Set ℂ} (hA : MeasurableSet A) (hAc : IsCompact (closure A))
    (hAU : closure A ⊆ U) (hfront : ν (frontier A) = 0) :
    Tendsto (fun i => μ i A) l (𝓝 (ν A)) := by
  obtain ⟨ψ, hψ, hψc, hψU, hψn, hψ1⟩ :=
    SmoothMeasureMass.exists_smooth_cutoff hAc hU hAU
  let ρ : Measure ℂ → Measure ℂ := fun m => m.withDensity (fun z => ENNReal.ofReal (ψ z))
  have hρν : IsFiniteMeasure (ρ ν) := finite_withDensity hψ.continuous hψc hψn
  have hρμ : ∀ i, IsFiniteMeasure (ρ (μ i)) := fun i =>
    finite_withDensity hψ.continuous hψc hψn
  let μf : ι → FiniteMeasure ℂ := fun i => ⟨ρ (μ i), hρμ i⟩
  let νf : FiniteMeasure ℂ := ⟨ρ ν, hρν⟩
  have ht : Tendsto μf l (𝓝 νf) := by
    apply FiniteMeasure.tendsto_of_forall_integral_tendsto
    intro f
    change Tendsto (fun i => ∫ z, f z ∂ρ (μ i)) l (𝓝 (∫ z, f z ∂ρ ν))
    simp only [ρ, integral_withDensity_cutoff _ hψ.continuous hψn]
    exact htest (fun z => ψ z * f z) (hψ.continuous.mul f.continuous)
      hψc.mul_right (tsupport_mul_subset_left.trans hψU)
  have hf : νf (frontier A) = 0 := by
    apply (FiniteMeasure.null_iff_toMeasure_null νf (frontier A)).mpr
    exact (withDensity_absolutelyContinuous ν _).null_mono hfront
  have hconv := finiteMeasure_tendsto_null_frontier ht hf
  have he : ∀ m : Measure ℂ, ρ m A = m A := fun m =>
    withDensity_cutoff_apply m hA (fun z hz => hψ1 z (subset_closure hz))
  have hcoe := ENNReal.continuous_coe.tendsto (νf A) |>.comp hconv
  have heμ : ∀ i, ((μf i A : ℝ≥0) : ℝ≥0∞) = μ i A := fun i =>
    (FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure (μf i) A).trans (he (μ i))
  have heν : ((νf A : ℝ≥0) : ℝ≥0∞) = ν A :=
    (FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure νf A).trans (he ν)
  change Tendsto (fun i => ((μf i A : ℝ≥0) : ℝ≥0∞)) l (𝓝 ((νf A : ℝ≥0) : ℝ≥0∞)) at hcoe
  simpa only [heμ, heν] using hcoe

/-- The smooth-test criterion followed by genuine local Portmanteau. -/
theorem tendsto_measure_of_smooth_compact_tests
    {ι : Type*} {l : Filter ι} {μ : ι → Measure ℂ} {ν : Measure ℂ}
    [∀ i, IsFiniteMeasureOnCompacts (μ i)] [IsFiniteMeasureOnCompacts ν]
    {U : Set ℂ} (hU : IsOpen U)
    (htest : ∀ f : ℂ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ U →
      Tendsto (fun i => ∫ z, f z ∂μ i) l (𝓝 (∫ z, f z ∂ν)))
    {A : Set ℂ} (hA : MeasurableSet A) (hAc : IsCompact (closure A))
    (hAU : closure A ⊆ U) (hfront : ν (frontier A) = 0) :
    Tendsto (fun i => μ i A) l (𝓝 (ν A)) :=
  tendsto_measure_of_continuous_compact_tests hU
    (fun _ hf hfc hfs => ContinuousMeasureTests.continuous_test_tendsto_of_smooth
      hU htest hf hfc hfs) hA hAc hAU hfront

#print axioms finiteMeasure_tendsto_null_frontier
#print axioms tendsto_measure_of_smooth_compact_tests
end V10.LocalPortmanteau
