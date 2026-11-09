import V10.ProjectionWindowTransport

/-! Actual absolute logarithmic loss on invertible real-affine windows.
The signed average controls the loss by an operator-norm upper bound; no
absolute-loss convergence or finiteness is assumed. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace V10.ProjectionWindowLoss
open HolomorphicProjectionAverage ProjectionAffineWindow HolomorphicProjectionSeries
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem weighted_absolute_integrable {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφn : ∀ z, 0 ≤ φ z) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    Integrable (fun z => φ z * |logProjection (fun w => F (window A b w)) c z|) := by
  have hi := (weighted_logProjection_integrable_window hF hFn ha hn hφ hφc A b).norm
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφn _)] using hi

/-- The genuine positive-part estimate for the actual integral, including
all isolated scalar zeros through the established local integrability. -/
theorem weighted_absolute_le {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφn : ∀ z, 0 ≤ φ z) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ)
    {B : ℝ} (hB : 1 < B) (hcB : c ∈ ball 0 B) :
    (∫ z, φ z * |logProjection (fun w => F (window A b w)) c z|) ≤
      2 * (∫ z, φ z) * Real.log B -
        averagedLogProjection (fun w => F (window A b w)) φ c := by
  let G := fun z => F (window A b z)
  have hi := weighted_logProjection_integrable_window hF hFn ha hn hφ hφc A b
  have hu : Integrable (fun z => φ z * (2 * Real.log B)) :=
    (hφ.integrable_of_hasCompactSupport hφc).mul_const _
  calc
    _ ≤ ∫ z, φ z * (2 * Real.log B) - φ z * logProjection G c z := by
      apply integral_mono (weighted_absolute_integrable hF hFn ha hn hφ hφc hφn A b)
        (hu.sub hi)
      intro z
      have hz := logProjection_le (fun w => hFn (window A b w)) hB hcB z
      have habs : |logProjection G c z| ≤ 2 * Real.log B - logProjection G c z :=
        abs_le.mpr ⟨by linarith [Real.log_nonneg hB.le], by linarith⟩
      change φ z * |logProjection G c z| ≤
        φ z * (2 * Real.log B) - φ z * logProjection G c z
      calc
        _ ≤ φ z * (2 * Real.log B - logProjection G c z) :=
          mul_le_mul_of_nonneg_left habs (hφn z)
        _ = _ := by ring
    _ = _ := by
      rw [integral_sub hu hi, integral_mul_const]
      unfold averagedLogProjection
      dsimp [G]
      ring

/-- Convergence of the actual signed averages implies convergence of the
actual weighted absolute loss, since the reciprocal normalizations vanish. -/
theorem weighted_absolute_tendsto {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφn : ∀ z, 0 ≤ φ z) (A : ℕ → ℂ ≃L[ℝ] ℂ) (b : ℕ → ℂ)
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹))
    (hv : Tendsto (fun m => (Q m)⁻¹ *
      averagedLogProjection (fun z => F (window (A m) (b m) z)) φ c) atTop (𝓝 0)) :
    Tendsto (fun m => (Q m)⁻¹ *
      ∫ z, φ z * |logProjection (fun w => F (window (A m) (b m) w)) c z|)
      atTop (𝓝 0) := by
  let B : ℝ := ‖c‖ + 2
  have hB : 1 < B := by dsimp [B]; linarith [norm_nonneg c]
  have hcB : c ∈ ball 0 B := by rw [mem_ball_zero_iff]; dsimp [B]; linarith
  apply squeeze_zero
    (fun m => mul_nonneg (inv_nonneg.mpr (hQ m).le)
      (integral_nonneg fun z => mul_nonneg (hφn z) (abs_nonneg _)))
    (fun m => mul_le_mul_of_nonneg_left
      (weighted_absolute_le hF hFn ha hn hφ hφc hφn (A m) (b m) hB hcB)
      (inv_nonneg.mpr (hQ m).le))
  have ht := (hQs.tendsto_atTop_zero.mul_const (2 * (∫ z, φ z) * Real.log B)).sub hv
  simpa only [zero_mul, sub_zero, mul_sub] using ht

#print axioms weighted_absolute_le
#print axioms weighted_absolute_tendsto
end V10.ProjectionWindowLoss
