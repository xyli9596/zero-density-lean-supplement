import V10.LogPoincareLelong

/-! Actual finite analytic zero measures and their proved Laplacian identity. -/
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace V10.AnalyticZeroMeasure
open ScalarCompactnessDivisor LogPoincareLelong

/-- The actual analytic divisor on a disk, as a finite positive atomic measure.
The positive-part convention is immaterial under analyticity, where every divisor
multiplicity is nonnegative. -/
def divisorMeasure (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : Measure ℂ :=
  ∑ u ∈ divisorSupport f c R,
    ((MeromorphicOn.divisor f (closedBall c R) u).toNat : ℝ≥0∞) • Measure.dirac u

instance divisorMeasure_finite (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    IsFiniteMeasure (divisorMeasure f c R) := by
  constructor
  simp only [divisorMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  simp

theorem integrable_divisorMeasure (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (φ : ℂ → ℝ) :
    Integrable φ (divisorMeasure f c R) := by
  apply integrable_finsetSum_measure.mpr
  intro u hu
  exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

/-- Integration against this measure is the actual multiplicity-weighted sum. -/
theorem integral_divisorMeasure {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (φ : ℂ → ℝ) :
    (∫ z, φ z ∂divisorMeasure f c R) =
      ∑ u ∈ divisorSupport f c R, (MeromorphicOn.divisor f (closedBall c R) u : ℝ) * φ u := by
  unfold divisorMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [integral_smul_measure, integral_dirac]
    simp only [ENNReal.toReal_natCast, smul_eq_mul]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u)
  · intro u hu
    exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

/-- Local Poincaré–Lelong with the actual positive zero-counting measure. -/
theorem analytic_log_laplacian_measure {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hw : w ∈ closedBall c R) (hfw : f w ≠ 0)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ closedBall c R) :
    (∫ z, Laplacian.laplacian φ z * Real.log ‖f z‖) =
      2 * Real.pi * ∫ z, φ z ∂divisorMeasure f c R := by
  rw [integral_divisorMeasure hf]
  exact analytic_log_laplacian hf hw hfw hφ hφc hs

/-- The zero measure normalized by the positive logarithmic scale. -/
def normalizedDivisorMeasure (f : ℂ → ℂ) (c : ℂ) (R q : ℝ) : Measure ℂ :=
  ENNReal.ofReal q⁻¹ • divisorMeasure f c R

instance normalizedDivisorMeasure_finite (f : ℂ → ℂ) (c : ℂ) (R q : ℝ) :
    IsFiniteMeasure (normalizedDivisorMeasure f c R q) := by
  exact (divisorMeasure f c R).smul_finite ENNReal.ofReal_ne_top

theorem normalized_log_laplacian_measure {f : ℂ → ℂ} {c w : ℂ} {R q : ℝ}
    (hq : 0 < q) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hw : w ∈ closedBall c R) (hfw : f w ≠ 0)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ closedBall c R) :
    (∫ z, Laplacian.laplacian φ z * (Real.log ‖f z‖ / q)) =
      2 * Real.pi * ∫ z, φ z ∂normalizedDivisorMeasure f c R q := by
  simp_rw [← mul_div_assoc]
  rw [integral_div, analytic_log_laplacian_measure hf hw hfw hφ hφc hs,
    normalizedDivisorMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hq.le), smul_eq_mul]
  ring

#print axioms analytic_log_laplacian_measure
#print axioms normalized_log_laplacian_measure
end V10.AnalyticZeroMeasure
