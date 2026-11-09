import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!
# The analytic input for v10 Corollary 7.5

We prove facts about the actual Bochner integral `∫ ξ, ρ ξ * exp (ξ * z) ∂μ`,
where `μ` is a positive measure, `ρ` is integrable, and frequencies are bounded
`μ`-almost everywhere. No analyticity or growth conclusion is a hypothesis.
The second half reconstructs an arbitrary finite-variation complex measure
from its Radon--Nikodym derivative with respect to variation, and identifies
the exact variation mass. The complex-measure integral is defined through this
proven representation. The zero counting conclusion still needs Theorem 1.6.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace V10.ContinuousFrequency
noncomputable section
variable {μ : Measure ℂ} {ρ : ℂ → ℂ} {σ : ℝ}

/-- The `n`th frequency moment of the actual Laplace integral. -/
def moment (μ : Measure ℂ) (ρ : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ ξ, ρ ξ * ξ ^ n * Complex.exp (ξ * z) ∂μ

/-- The continuous-frequency perturbation. -/
def transform (μ : Measure ℂ) (ρ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ ξ, ρ ξ * Complex.exp (ξ * z) ∂μ

/-- The density mass; for a polar density this is variation mass. -/
def densityMass (μ : Measure ℂ) (ρ : ℂ → ℂ) : ℝ := ∫ ξ, ‖ρ ξ‖ ∂μ

lemma densityMass_nonneg : 0 ≤ densityMass μ ρ := integral_nonneg fun _ ↦ norm_nonneg _

@[simp] lemma moment_zero : moment μ ρ 0 = transform μ ρ := by
  funext z
  simp [moment, transform]

lemma norm_exp_mul_le {ξ z : ℂ} (hξ : ‖ξ‖ ≤ σ) :
    ‖Complex.exp (ξ * z)‖ ≤ Real.exp (σ * ‖z‖) := by
  calc
    ‖Complex.exp (ξ * z)‖ ≤ Real.exp ‖ξ * z‖ := Complex.norm_exp_le_exp_norm _
    _ ≤ Real.exp (σ * ‖z‖) := by
      apply Real.exp_le_exp.mpr
      simpa only [norm_mul] using mul_le_mul_of_nonneg_right hξ (norm_nonneg z)

lemma norm_integrand_le (hσ : 0 ≤ σ) (n : ℕ) {ξ z : ℂ} (hξ : ‖ξ‖ ≤ σ) :
    ‖ρ ξ * ξ ^ n * Complex.exp (ξ * z)‖ ≤
      ‖ρ ξ‖ * σ ^ n * Real.exp (σ * ‖z‖) := by
  rw [norm_mul, norm_mul, norm_pow]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg ξ) hξ n) (norm_nonneg _)
  · exact norm_exp_mul_le hξ
  · exact norm_nonneg _
  · exact mul_nonneg (norm_nonneg _) (pow_nonneg hσ _)

lemma integrand_aestronglyMeasurable (hρ : Integrable ρ μ) (n : ℕ) (z : ℂ) :
    AEStronglyMeasurable (fun ξ ↦ ρ ξ * ξ ^ n * Complex.exp (ξ * z)) μ := by
  exact (hρ.aestronglyMeasurable.mul
    ((continuous_id.pow n).aestronglyMeasurable)).mul
    ((Complex.continuous_exp.comp (continuous_id.mul_const z)).aestronglyMeasurable)

lemma integrand_integrable (hρ : Integrable ρ μ) (hσ : 0 ≤ σ)
    (hsupp : ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ σ) (n : ℕ) (z : ℂ) :
    Integrable (fun ξ ↦ ρ ξ * ξ ^ n * Complex.exp (ξ * z)) μ := by
  apply ((hρ.norm.mul_const (σ ^ n)).mul_const (Real.exp (σ * ‖z‖))).mono'
    (integrand_aestronglyMeasurable hρ n z)
  filter_upwards [hsupp] with ξ hξ
  exact norm_integrand_le hσ n hξ

/-- Uniform exponential bound for every moment, with the actual density mass. -/
theorem norm_moment_le (hρ : Integrable ρ μ) (hσ : 0 ≤ σ)
    (hsupp : ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ σ) (n : ℕ) (z : ℂ) :
    ‖moment μ ρ n z‖ ≤ densityMass μ ρ * σ ^ n * Real.exp (σ * ‖z‖) := by
  calc
    ‖moment μ ρ n z‖ ≤ ∫ ξ, ‖ρ ξ‖ * σ ^ n * Real.exp (σ * ‖z‖) ∂μ := by
      apply norm_integral_le_of_norm_le
        ((hρ.norm.mul_const (σ ^ n)).mul_const (Real.exp (σ * ‖z‖)))
      filter_upwards [hsupp] with ξ hξ
      exact norm_integrand_le hσ n hξ
    _ = _ := by simp only [integral_mul_const, densityMass]

/-- The global manuscript bound, with no assumed asymptotic premise. -/
theorem norm_transform_le (hρ : Integrable ρ μ) (hσ : 0 ≤ σ)
    (hsupp : ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ σ) (z : ℂ) :
    ‖transform μ ρ z‖ ≤ densityMass μ ρ * Real.exp (σ * ‖z‖) := by
  simpa using norm_moment_le hρ hσ hsupp 0 z

lemma hasDerivAt_integrand (n : ℕ) (ξ z : ℂ) :
    HasDerivAt (fun w ↦ ρ ξ * ξ ^ n * Complex.exp (ξ * w))
      (ρ ξ * ξ ^ (n + 1) * Complex.exp (ξ * z)) z := by
  have h := (((hasDerivAt_id z).const_mul ξ).cexp.const_mul (ρ ξ * ξ ^ n))
  simpa only [id_eq, mul_one, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

/-- Differentiation under the actual integral, justified on a fixed ball by
an integrable majorant. -/
theorem hasDerivAt_moment (hρ : Integrable ρ μ) (hσ : 0 ≤ σ)
    (hsupp : ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ σ) (n : ℕ) (z : ℂ) :
    HasDerivAt (moment μ ρ n) (moment μ ρ (n + 1) z) z := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Metric.ball z 1)
    (F := fun w ξ ↦ ρ ξ * ξ ^ n * Complex.exp (ξ * w))
    (F' := fun w ξ ↦ ρ ξ * ξ ^ (n + 1) * Complex.exp (ξ * w))
    (bound := fun ξ ↦ ‖ρ ξ‖ * σ ^ (n + 1) * Real.exp (σ * (‖z‖ + 1)))
    (Metric.ball_mem_nhds z (by norm_num))
    (Filter.Eventually.of_forall (integrand_aestronglyMeasurable hρ n))
    (integrand_integrable hρ hσ hsupp n z)
    (integrand_aestronglyMeasurable hρ (n + 1) z) ?_
    ((hρ.norm.mul_const (σ ^ (n + 1))).mul_const (Real.exp (σ * (‖z‖ + 1)))) ?_).2
  · filter_upwards [hsupp] with ξ hξ
    intro w hw
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have hd : ‖w - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
      have ht := norm_le_norm_sub_add w z
      linarith
    calc
      ‖ρ ξ * ξ ^ (n + 1) * Complex.exp (ξ * w)‖ ≤
          ‖ρ ξ‖ * σ ^ (n + 1) * Real.exp (σ * ‖w‖) := norm_integrand_le hσ _ hξ
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw' hσ))
        (mul_nonneg (norm_nonneg _) (pow_nonneg hσ _))
  · exact Filter.Eventually.of_forall fun ξ w _ ↦ hasDerivAt_integrand n ξ w

/-- Entire analyticity follows from the complex differentiability just proved. -/
theorem analyticOnNhd_transform (hρ : Integrable ρ μ) (hσ : 0 ≤ σ)
    (hsupp : ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ σ) : AnalyticOnNhd ℂ (transform μ ρ) Set.univ := by
  have hd : Differentiable ℂ (transform μ ρ) := by
    intro z
    simpa using (hasDerivAt_moment hρ hσ hsupp 0 z).differentiableAt
  exact hd.differentiableOn.analyticOnNhd isOpen_univ

/-- Formula for all derivative orders, not merely existence. -/
theorem iteratedDeriv_transform (hρ : Integrable ρ μ) (hσ : 0 ≤ σ)
    (hsupp : ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ σ) (n : ℕ) :
    iteratedDeriv n (transform μ ρ) = moment μ ρ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      exact (hasDerivAt_moment hρ hσ hsupp n z).deriv

/-- Every derivative enjoys the same exponential type bound. -/
theorem norm_iteratedDeriv_transform_le (hρ : Integrable ρ μ) (hσ : 0 ≤ σ)
    (hsupp : ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ σ) (n : ℕ) (z : ℂ) :
    ‖iteratedDeriv n (transform μ ρ) z‖ ≤
      densityMass μ ρ * σ ^ n * Real.exp (σ * ‖z‖) := by
  rw [iteratedDeriv_transform hρ hσ hsupp]
  exact norm_moment_le hρ hσ hsupp n z

/-- Epsilon formulation of upper exponential type at most `σ`.
The multiplicative mass is absorbed outside an explicitly finite radius. -/
theorem exponential_type_bound (hρ : Integrable ρ μ) (hσ : 0 ≤ σ)
    (hsupp : ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖transform μ ρ z‖ ≤ Real.exp ((σ + ε) * ‖z‖) := by
  refine ⟨densityMass μ ρ / ε, div_nonneg densityMass_nonneg hε.le, ?_⟩
  intro z hz
  have hm : densityMass μ ρ ≤ ε * ‖z‖ := by
    have := (div_le_iff₀ hε).mp hz
    simpa only [mul_comm] using this
  have he : densityMass μ ρ ≤ Real.exp (ε * ‖z‖) := by
    linarith [Real.add_one_le_exp (ε * ‖z‖)]
  calc
    ‖transform μ ρ z‖ ≤ densityMass μ ρ * Real.exp (σ * ‖z‖) :=
      norm_transform_le hρ hσ hsupp z
    _ ≤ Real.exp (ε * ‖z‖) * Real.exp (σ * ‖z‖) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp ((σ + ε) * ‖z‖) := by rw [← Real.exp_add]; congr 1; ring

/-- For a polar density the mass is exactly the mass of the positive measure,
which is intended to be the total-variation measure. -/
theorem densityMass_eq_measure [IsFiniteMeasure μ]
    (hρ : ∀ᵐ ξ ∂μ, ‖ρ ξ‖ = 1) : densityMass μ ρ = μ.real Set.univ := by
  unfold densityMass
  rw [integral_congr_ae hρ]
  simp

/-- This identifies the proven bound with the actual variation of the complex
vector measure constructed from an integrable density. -/
theorem densityMass_eq_variation (hρ : Integrable ρ μ) :
    densityMass μ ρ = (μ.withDensityᵥ ρ).variation.real Set.univ := by
  rw [Measure.variation_withDensityᵥ hρ, measureReal_def,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact integral_norm_eq_lintegral_enorm hρ.aestronglyMeasurable

/-- Exact total-variation constant for the represented complex measure. -/
theorem norm_transform_le_variation (hρ : Integrable ρ μ) (hσ : 0 ≤ σ)
    (hsupp : ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ σ) (z : ℂ) :
    ‖transform μ ρ z‖ ≤ (μ.withDensityᵥ ρ).variation.real Set.univ *
      Real.exp (σ * ‖z‖) := by
  rw [← densityMass_eq_variation hρ]
  exact norm_transform_le hρ hσ hsupp z

/-- Compact frequency support suffices for entire analyticity. -/
theorem analyticOnNhd_transform_of_compact (hρ : Integrable ρ μ)
    {K : Set ℂ} (hK : IsCompact K) (hsupp : ∀ᵐ ξ ∂μ, ξ ∈ K) :
    AnalyticOnNhd ℂ (transform μ ρ) Set.univ := by
  obtain ⟨σ, hσ, hbound⟩ := hK.isBounded.exists_pos_norm_le
  apply analyticOnNhd_transform hρ hσ.le
  filter_upwards [hsupp] with ξ hξ
  exact hbound ξ hξ

/-- Radon--Nikodym reconstruction of a complex measure from its variation.
This proves the representation rather than assuming it. -/
theorem complexMeasure_withDensity_rnDeriv (ν : ComplexMeasure ℂ)
    [IsFiniteMeasure ν.variation] :
    ν.variation.withDensityᵥ (ν.rnDeriv ν.variation) = ν := by
  have habs : ν ≪ᵥ ν.variation.toENNRealVectorMeasure := ν.absolutelyContinuous
  obtain ⟨hre, him⟩ := (ComplexMeasure.absolutelyContinuous_ennreal_iff ν _).mp habs
  have hr := ν.re.withDensityᵥ_rnDeriv_eq ν.variation hre
  have hi := ν.im.withDensityᵥ_rnDeriv_eq ν.variation him
  have hint := ν.integrable_rnDeriv ν.variation
  ext s hs : 1
  rw [withDensityᵥ_apply hint hs]
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re hint.integrableOn,
      RCLike.re_eq_complex_re]
    change (∫ x in s, ν.re.rnDeriv ν.variation x ∂ν.variation) = (ν s).re
    rw [← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs, hr]
    rfl
  · rw [← RCLike.im_eq_complex_im, ← integral_im hint.integrableOn,
      RCLike.im_eq_complex_im]
    change (∫ x in s, ν.im.rnDeriv ν.variation x ∂ν.variation) = (ν s).im
    rw [← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs, hi]
    rfl

/-- Laplace transform of a finite-variation complex measure, using its proven
Radon--Nikodym representation relative to variation. -/
def complexTransform (ν : ComplexMeasure ℂ) (z : ℂ) : ℂ :=
  transform ν.variation (ν.rnDeriv ν.variation) z

/-- The exact total-variation bound for an arbitrary finite-variation complex measure. -/
theorem norm_complexTransform_le (ν : ComplexMeasure ℂ) [IsFiniteMeasure ν.variation]
    (hσ : 0 ≤ σ) (hsupp : ∀ᵐ ξ ∂ν.variation, ‖ξ‖ ≤ σ) (z : ℂ) :
    ‖complexTransform ν z‖ ≤ ν.variation.real Set.univ * Real.exp (σ * ‖z‖) := by
  have h := norm_transform_le_variation (ν.integrable_rnDeriv ν.variation) hσ hsupp z
  rw [complexMeasure_withDensity_rnDeriv ν] at h
  exact h

/-- Entire analyticity for arbitrary finite-variation complex frequency measures. -/
theorem analyticOnNhd_complexTransform (ν : ComplexMeasure ℂ)
    (hσ : 0 ≤ σ) (hsupp : ∀ᵐ ξ ∂ν.variation, ‖ξ‖ ≤ σ) :
    AnalyticOnNhd ℂ (complexTransform ν) Set.univ :=
  analyticOnNhd_transform (ν.integrable_rnDeriv ν.variation) hσ hsupp

/-- Upper type at most the frequency radius, for the complex-measure transform. -/
theorem complexTransform_exponential_type_bound (ν : ComplexMeasure ℂ)
    (hσ : 0 ≤ σ) (hsupp : ∀ᵐ ξ ∂ν.variation, ‖ξ‖ ≤ σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖complexTransform ν z‖ ≤ Real.exp ((σ + ε) * ‖z‖) :=
  exponential_type_bound (ν.integrable_rnDeriv ν.variation) hσ hsupp hε

/-- The maximum modulus of the compact frequency set (defined as a supremum). -/
def frequencyRadius (K : Set ℂ) : ℝ := sSup (norm '' K)

lemma norm_le_frequencyRadius {K : Set ℂ} (hK : IsCompact K) {ξ : ℂ} (hξ : ξ ∈ K) :
    ‖ξ‖ ≤ frequencyRadius K :=
  le_csSup (hK.image continuous_norm).bddAbove (mem_image_of_mem _ hξ)

lemma frequencyRadius_nonneg {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) :
    0 ≤ frequencyRadius K := by
  obtain ⟨ξ, hξ⟩ := hne
  exact (norm_nonneg ξ).trans (norm_le_frequencyRadius hK hξ)

/-- On a nonempty compact set this supremum is the actual maximum. -/
theorem frequencyRadius_attained {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ ξ ∈ K, frequencyRadius K = ‖ξ‖ :=
  hK.exists_sSup_image_eq hne continuous_norm.continuousOn

/-- The analytic input of Corollary 7.5 for an arbitrary complex measure:
entire analyticity and the exact total-variation constant on its compact support. -/
theorem compact_frequency_analytic_input (ν : ComplexMeasure ℂ)
    [IsFiniteMeasure ν.variation] {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hsupp : ν.variation Kᶜ = 0) :
    AnalyticOnNhd ℂ (complexTransform ν) Set.univ ∧
    ∀ z : ℂ, ‖complexTransform ν z‖ ≤
      ν.variation.real K * Real.exp (frequencyRadius K * ‖z‖) := by
  have hae : ∀ᵐ ξ ∂ν.variation, ξ ∈ K := ae_iff.mpr hsupp
  have hbound : ∀ᵐ ξ ∂ν.variation, ‖ξ‖ ≤ frequencyRadius K :=
    hae.mono fun ξ hξ ↦ norm_le_frequencyRadius hK hξ
  have hσ := frequencyRadius_nonneg hK hne
  refine ⟨analyticOnNhd_complexTransform ν hσ hbound, ?_⟩
  intro z
  have hm : ν.variation K = ν.variation Set.univ := by
    have hadd := measure_add_measure_compl (μ := ν.variation) hK.measurableSet
    simpa only [hsupp, add_zero] using hadd
  simpa only [measureReal_def, hm] using norm_complexTransform_le ν hσ hbound z

/-- The epsilon type bound at the exact compact frequency radius. -/
theorem compact_frequency_type_bound (ν : ComplexMeasure ℂ)
    [IsFiniteMeasure ν.variation] {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hsupp : ν.variation Kᶜ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖complexTransform ν z‖ ≤ Real.exp ((frequencyRadius K + ε) * ‖z‖) := by
  have hae : ∀ᵐ ξ ∂ν.variation, ξ ∈ K := ae_iff.mpr hsupp
  exact complexTransform_exponential_type_bound ν (frequencyRadius_nonneg hK hne)
    (hae.mono fun ξ hξ ↦ norm_le_frequencyRadius hK hξ) hε

end
end V10.ContinuousFrequency
