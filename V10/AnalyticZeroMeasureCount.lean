import V10.AnalyticZeroMeasure
import ZeroDensity.CountGeometry

/-! The constructed divisor measure has exactly the existing actual zero count
as its mass on each region; no new surrogate count is introduced. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace V10.AnalyticZeroMeasureCount
attribute [local instance] Classical.propDecidable
open AnalyticZeroMeasure ScalarCompactnessDivisor

/-- Region mass is the sum of actual analytic multiplicities in that region. -/
theorem divisorMeasure_real_apply {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (A : Set ℂ) :
    (divisorMeasure f c R).real A =
      ∑ u ∈ divisorSupport f c R,
        if u ∈ A then (MeromorphicOn.divisor f (closedBall c R) u : ℝ) else 0 := by
  classical
  unfold Measure.real divisorMeasure
  rw [Measure.finsetSum_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro u hu
    by_cases h : u ∈ A
    · simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
        Set.indicator_of_mem h, Pi.one_apply, mul_one, ENNReal.toReal_natCast, if_pos h]
      exact_mod_cast Int.toNat_of_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u)
    · simp [Measure.smul_apply, Measure.dirac_apply, h]
  · intro u hu
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)

/-- The new positive zero measure agrees with the existing `CountGeometry.count`. -/
theorem divisorMeasure_real_eq_count {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (A : Set ℂ) :
    (divisorMeasure f 0 R).real A = ZeroDensity.CountGeometry.count f A R := by
  classical
  rw [divisorMeasure_real_apply hf, ZeroDensity.CountGeometry.count]
  have hs : Function.support (fun u => if u ∈ A then
      MeromorphicOn.divisor f (closedBall (0 : ℂ) R) u else (0 : ℤ)) ⊆
        (divisorSupport f 0 R : Set ℂ) := by
    intro u hu
    apply mem_divisorSupport.mpr
    by_contra hz
    apply hu
    simp [hz]
  rw [finsum_eq_sum_of_support_subset _ hs, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs <;> simp

/-- Normalized zero-measure mass is the actual zero count divided by its scale. -/
theorem normalizedDivisorMeasure_real_eq_count {f : ℂ → ℂ} {R q : ℝ}
    (hq : 0 < q) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (A : Set ℂ) :
    (normalizedDivisorMeasure f 0 R q).real A = ZeroDensity.CountGeometry.count f A R / q := by
  rw [Measure.real, normalizedDivisorMeasure, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hq.le)]
  change q⁻¹ * (divisorMeasure f 0 R).real A = _
  rw [divisorMeasure_real_eq_count hf]
  ring

#print axioms divisorMeasure_real_eq_count
#print axioms normalizedDivisorMeasure_real_eq_count
end V10.AnalyticZeroMeasureCount
