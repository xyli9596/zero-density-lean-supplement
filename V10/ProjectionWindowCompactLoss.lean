import V10.ProjectionWindowLoss
import Mathlib.Tactic

/-! From actual logarithmic cutoff losses to unweighted compact-window
losses. The compact integral is proved finite by domination before integral
comparison; no totalized nonintegrable integral is used. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace V10.ProjectionWindowCompactLoss
open HolomorphicProjectionAverage ProjectionAffineWindow ProjectionWindowLoss
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem measurable_absolute_window {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) (c : E) :
    Measurable (fun z => |logProjection (fun w => F (window A b w)) c z|) := by
  have hG := hF.comp (window A b).continuous
  exact ((hG.clm_apply continuous_const).measurable.norm.div hG.measurable.norm).log.abs

/-- The actual unweighted absolute logarithmic loss is integrable on the
compact set because the actual integrable cutoff dominates it there. -/
theorem compact_absolute_integrable {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφn : ∀ z, 0 ≤ φ z) {K : Set ℂ} (hK : IsCompact K)
    (hφK : ∀ z ∈ K, 1 ≤ φ z) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    IntegrableOn (fun z => |logProjection (fun w => F (window A b w)) c z|) K volume := by
  have hi := weighted_absolute_integrable hF hFn ha hn hφ hφc hφn A b
  apply hi.restrict.mono' (measurable_absolute_window hF A b c).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  simp only [Real.norm_eq_abs, abs_abs]
  exact le_mul_of_one_le_left (abs_nonneg _) (hφK z hz)

/-- Actual integral domination, after both integrability obligations have
been discharged from the original analytic family and affine window. -/
theorem compact_absolute_le_weighted {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφn : ∀ z, 0 ≤ φ z) {K : Set ℂ} (hK : IsCompact K)
    (hφK : ∀ z ∈ K, 1 ≤ φ z) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    (∫ z in K, |logProjection (fun w => F (window A b w)) c z|) ≤
      ∫ z, φ z * |logProjection (fun w => F (window A b w)) c z| := by
  have hi := weighted_absolute_integrable hF hFn ha hn hφ hφc hφn A b
  calc
    _ ≤ ∫ z in K, φ z * |logProjection (fun w => F (window A b w)) c z| := by
      apply integral_mono_ae
        (compact_absolute_integrable hF hFn ha hn hφ hφc hφn hK hφK A b) hi.restrict
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      exact le_mul_of_one_le_left (abs_nonneg _) (hφK z hz)
    _ ≤ _ := setIntegral_le_integral hi
      (ae_of_all _ fun z => mul_nonneg (hφn z) (abs_nonneg _))

/-- Intermediate domination endpoint: weighted absolute convergence implies
the actual unweighted compact convergence; compact integrability is derived. -/
theorem compact_absolute_tendsto_of_weighted {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφn : ∀ z, 0 ≤ φ z) {K : Set ℂ} (hK : IsCompact K)
    (hφK : ∀ z ∈ K, 1 ≤ φ z) (A : ℕ → ℂ ≃L[ℝ] ℂ) (b : ℕ → ℂ)
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m)
    (hw : Tendsto (fun m => (Q m)⁻¹ *
      ∫ z, φ z * |logProjection (fun w => F (window (A m) (b m) w)) c z|)
      atTop (𝓝 0)) :
    Tendsto (fun m => (Q m)⁻¹ *
      ∫ z in K, |logProjection (fun w => F (window (A m) (b m) w)) c z|)
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun m => mul_nonneg (inv_nonneg.mpr (hQ m).le) (integral_nonneg fun _ => abs_nonneg _))
    (fun m => mul_le_mul_of_nonneg_left
      (compact_absolute_le_weighted hF hFn ha hn hφ hφc hφn hK hφK (A m) (b m))
      (inv_nonneg.mpr (hQ m).le)) hw

/-- The actual compact-window absolute loss tends to zero from the signed
average and summable inverse normalizations. No absolute-loss convergence,
weighted or unweighted, is assumed by this endpoint. -/
theorem compact_absolute_tendsto_of_signed {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφn : ∀ z, 0 ≤ φ z) {K : Set ℂ} (hK : IsCompact K)
    (hφK : ∀ z ∈ K, 1 ≤ φ z) (A : ℕ → ℂ ≃L[ℝ] ℂ) (b : ℕ → ℂ)
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹))
    (hv : Tendsto (fun m => (Q m)⁻¹ *
      averagedLogProjection (fun z => F (window (A m) (b m) z)) φ c) atTop (𝓝 0)) :
    Tendsto (fun m => (Q m)⁻¹ *
      ∫ z in K, |logProjection (fun w => F (window (A m) (b m) w)) c z|)
      atTop (𝓝 0) :=
  compact_absolute_tendsto_of_weighted hF hFn ha hn hφ hφc hφn hK hφK A b hQ
    (weighted_absolute_tendsto hF hFn ha hn hφ hφc hφn A b hQ hQs hv)

#print axioms compact_absolute_integrable
#print axioms compact_absolute_le_weighted
#print axioms compact_absolute_tendsto_of_signed
end V10.ProjectionWindowCompactLoss
