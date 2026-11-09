import V10.ScaledDivisorCount
import ZeroDensity.SectorCount

/-!
# Dyadic accumulation for actual exterior-domain zero counts

Only compact annular carriers inside the original analytic domain are used.
The bounded inner remainder and count monotonicity are derived from the actual
nonnegative analytic divisor. No entire extension is assumed.
-/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace V10.ExteriorSectorCount
open RadialTransfer RadialCutoffGeometry DomainDivisorCount ScaledDivisorCount
open AnalyticZeroMeasureCompact ZeroDensity.SectorDivisorCount

/-- Actual exterior counts have the local boundedness needed for dyadic
accumulation; all boundedness comes from a larger compact analytic carrier. -/
theorem domainPhaseCount_bounded {v : ℂ → ℂ} {U : Set ℂ} {S a b c : ℝ}
    (hv : AnalyticOnNhd ℂ v U) (hcarrier : ∀ R, polarCarrier S R a b ⊆ U)
    (T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, ∀ t ∈ Icc T (2 * T), |domainPhaseCount v U S a b t - c * t| ≤ B := by
  refine ⟨phaseCount v S a b (2 * T) + |c| * (2 * T), ?_⟩
  intro t ht
  rw [domainPhaseCount_eq_phaseCount hv (hcarrier t)]
  have hn := phaseCount_nonneg (hv.mono (hcarrier t))
  have hu := phaseCount_mono_radius ht.2 (hv.mono (hcarrier (2 * T)))
  have ht0 : 0 ≤ t := (hT.trans_le ht.1).le
  calc
    |phaseCount v S a b t - c * t| ≤ |phaseCount v S a b t| + |c * t| := abs_sub _ _
    _ = phaseCount v S a b t + |c| * t := by rw [abs_of_nonneg hn, abs_mul, abs_of_nonneg ht0]
    _ ≤ _ := add_le_add hu (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg c))

/-- Dyadic annular asymptotics imply the full actual exterior sector count. -/
theorem domainPhaseCount_tendsto_of_annular {v : ℂ → ℂ} {U : Set ℂ} {S a b c : ℝ}
    (hv : AnalyticOnNhd ℂ v U) (hcarrier : ∀ R, polarCarrier S R a b ⊆ U)
    (hann : Tendsto (fun t : ℝ =>
      (domainPhaseCount v U S a b (2 * t) - domainPhaseCount v U S a b t) / t)
      atTop (𝓝 c)) :
    Tendsto (fun R : ℝ => domainPhaseCount v U S a b R / R) atTop (𝓝 c) :=
  ZeroDensity.SectorCount.radial_of_annular (domainPhaseCount_bounded hv hcarrier) hann

/-- Consumption of actual normalized zero-measure convergence on the dyadic
annulus. The counting law is a conclusion, not a supplied asymptotic. -/
theorem domainPhaseCount_tendsto_of_scaled_annulus
    {v : ℂ → ℂ} {U K : Set ℂ} (hK : IsCompact K) {S a b m : ℝ} (hS : 0 ≤ S)
    (hv : AnalyticOnNhd ℂ v U) (hcarrier : ∀ R, polarCarrier S R a b ⊆ U)
    (hmap : ∀ᶠ R : ℝ in atTop, MapsTo (fun z : ℂ => (R : ℂ) * z) K U)
    (hAK : clippedSector (1 / 2) 1 a b ⊆ K)
    (hmass : Tendsto (fun R : ℝ =>
      (normalizedDivisorMeasure (fun z => v ((R : ℂ) * z)) hK R).real
        (clippedSector (1 / 2) 1 a b)) atTop (𝓝 m)) :
    Tendsto (fun R : ℝ => domainPhaseCount v U S a b R / R) atTop (𝓝 (2 * m)) := by
  have hann : Tendsto (fun R : ℝ =>
      (domainPhaseCount v U S a b R - domainPhaseCount v U S a b (R / 2)) / R)
      atTop (𝓝 m) := by
    apply hmass.congr'
    filter_upwards [hmap, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (2 * S)] with R hmap hR hRS
    exact normalizedDivisorMeasure_real_annulus hK hS hR (by linarith) hv hmap hAK (hcarrier R)
  have ht : Tendsto (fun t : ℝ => 2 * t) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
  have ha := (hann.comp ht).const_mul 2
  apply domainPhaseCount_tendsto_of_annular hv hcarrier
  convert ha using 1
  ext t
  dsimp only [Function.comp_apply]
  rw [show 2 * t / 2 = t by ring]
  ring

#print axioms domainPhaseCount_tendsto_of_scaled_annulus
end V10.ExteriorSectorCount
