import V10.AnalyticZeroMeasureCompact
import V10.DomainDivisorCount

/-!
# Actual normalized divisor mass and dilation of exterior counts

The compact carrier may be any shape inside the scaled analytic domain. The
right side always uses the original analytic-domain divisor, so no analyticity
at the origin or at the domain's inner boundary is introduced.
-/
noncomputable section
open Set Filter MeasureTheory Metric MeromorphicOn
open scoped Topology ENNReal
namespace V10.ScaledDivisorCount
open AnalyticZeroMeasureCompact RadialTransfer RadialCutoffGeometry DomainDivisorCount
open ZeroDensity.SectorDivisorCount ZeroDensity.CountGeometry
attribute [local instance] Classical.propDecidable

/-- Mass of the compact-carrier measure is the actual filtered divisor sum. -/
theorem divisorMeasure_real_eq_regionCount {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K) (A : Set ℂ) :
    (divisorMeasure f hK).real A = regionCount f K A := by
  classical
  have hm : (divisorMeasure f hK).real A =
      ∑ u ∈ divisorSupport f hK, if u ∈ A then (divisor f K u : ℝ) else 0 := by
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
  rw [hm, regionCount]
  have hs : Function.support (fun u => if u ∈ A then divisor f K u else (0 : ℤ)) ⊆
      (divisorSupport f hK : Set ℂ) := by
    intro u hu
    apply (mem_divisorSupport hK).mpr
    by_contra hz
    apply hu
    simp [hz]
  rw [finsum_eq_sum_of_support_subset _ hs, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs <;> simp

/-- Dilation preserves every counted analytic multiplicity and the full
filtered finite sum, with the original divisor evaluated only in its domain. -/
theorem regionCount_dilation {v : ℂ → ℂ} {U K A : Set ℂ} {R : ℝ}
    (hR : 0 < R) (hv : AnalyticOnNhd ℂ v U)
    (hmap : MapsTo (fun z : ℂ => (R : ℂ) * z) K U) (hAK : A ⊆ K) :
    regionCount (fun z => v ((R : ℂ) * z)) K A =
      regionCount v U ((fun z : ℂ => (R : ℂ) * z) '' A) := by
  have hRn : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hinj : InjOn (fun z : ℂ => (R : ℂ) * z) A :=
    (mul_right_injective₀ hRn).injOn
  rw [regionCount_eq_mem_sum, regionCount_eq_mem_sum,
    finsum_mem_image hinj]
  congr 1
  apply finsum_mem_congr rfl
  intro z hz
  exact ZeroDensity.ConformalMultiplicity.divisor_comp hv
    (fun z _ => analyticAt_const.mul analyticAt_id) hmap (hAK hz)
    (by
      change deriv (fun w : ℂ => (R : ℂ) * w) z ≠ 0
      simpa only [deriv_const_mul_id] using hRn)

/-- Exact mass-to-original-count equality for a positive scale. -/
theorem normalizedDivisorMeasure_real_dilation {v : ℂ → ℂ} {U K A : Set ℂ}
    (hK : IsCompact K) {R : ℝ} (hR : 0 < R) (hv : AnalyticOnNhd ℂ v U)
    (hmap : MapsTo (fun z : ℂ => (R : ℂ) * z) K U) (hAK : A ⊆ K) :
    (normalizedDivisorMeasure (fun z => v ((R : ℂ) * z)) hK R).real A =
      regionCount v U ((fun z : ℂ => (R : ℂ) * z) '' A) / R := by
  have hscaled : AnalyticOnNhd ℂ (fun z => v ((R : ℂ) * z)) K :=
    fun z hz => (hv _ (hmap hz)).comp (analyticAt_const.mul analyticAt_id)
  rw [Measure.real, normalizedDivisorMeasure, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hR.le)]
  change R⁻¹ * (divisorMeasure (fun z => v ((R : ℂ) * z)) hK).real A = _
  rw [divisorMeasure_real_eq_regionCount hK hscaled,
    regionCount_dilation hR hv hmap hAK]
  ring

/-- Explicit polar representation retaining the open inner and angular sides
and the closed outer radial boundary. -/
theorem mem_clippedSector_iff {S T a b : ℝ} (hS : 0 ≤ S) (z : ℂ) :
    z ∈ clippedSector S T a b ↔
      ∃ r ∈ Ioc S T, ∃ θ ∈ Ioo a b,
        z = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [clippedSector_eq_norm hS]
  constructor
  · rintro ⟨⟨r, hr, θ, hθ, he⟩, hn⟩
    have hnr : ‖z‖ = r := by rw [he, norm_polar (hS.trans hr.le)]
    exact ⟨r, ⟨hr, hnr ▸ hn⟩, θ, hθ, he⟩
  · rintro ⟨r, hr, θ, hθ, he⟩
    refine ⟨⟨r, hr.1, θ, hθ, he⟩, ?_⟩
    change ‖z‖ ≤ T
    rw [he, norm_polar (hS.trans hr.1.le)]
    exact hr.2

/-- Positive real dilation scales both radial cutoffs exactly. -/
theorem dilation_clippedSector {S T a b R : ℝ} (hS : 0 ≤ S) (hR : 0 < R) :
    (fun z : ℂ => (R : ℂ) * z) '' clippedSector S T a b =
      clippedSector (R * S) (R * T) a b := by
  ext z
  rw [mem_clippedSector_iff (mul_nonneg hR.le hS)]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨r, hr, θ, hθ, he⟩ := (mem_clippedSector_iff hS w).mp hw
    refine ⟨R * r, ⟨mul_lt_mul_of_pos_left hr.1 hR, mul_le_mul_of_nonneg_left hr.2 hR.le⟩,
      θ, hθ, ?_⟩
    rw [he, Complex.ofReal_mul, mul_assoc]
  · rintro ⟨r, hr, θ, hθ, rfl⟩
    refine ⟨((r / R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I), ?_, ?_⟩
    · apply (mem_clippedSector_iff hS _).mpr
      refine ⟨r / R, ⟨?_, ?_⟩, θ, hθ, rfl⟩
      · exact (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using hr.1)
      · exact (div_le_iff₀ hR).mpr (by simpa only [mul_comm] using hr.2)
    · dsimp only
      rw [← mul_assoc, ← Complex.ofReal_mul]
      congr 2
      field_simp

/-- The dyadic annulus mass is exactly the difference of the two original
exterior sector counts, divided by R. All multiplicities are transported by
actual analytic dilation. -/
theorem normalizedDivisorMeasure_real_annulus {v : ℂ → ℂ} {U K : Set ℂ}
    (hK : IsCompact K) {R S a b : ℝ} (hS : 0 ≤ S) (hR : 0 < R)
    (hSR : S ≤ R / 2) (hv : AnalyticOnNhd ℂ v U)
    (hmap : MapsTo (fun z : ℂ => (R : ℂ) * z) K U)
    (hAK : clippedSector (1 / 2) 1 a b ⊆ K)
    (hcarrier : polarCarrier S R a b ⊆ U) :
    (normalizedDivisorMeasure (fun z => v ((R : ℂ) * z)) hK R).real
      (clippedSector (1 / 2) 1 a b) =
      (domainPhaseCount v U S a b R - domainPhaseCount v U S a b (R / 2)) / R := by
  rw [normalizedDivisorMeasure_real_dilation hK hR hv hmap hAK,
    dilation_clippedSector (by norm_num : (0 : ℝ) ≤ 1 / 2) hR,
    mul_one, show R * (1 / 2) = R / 2 by ring]
  have hhalf : R / 2 ≤ R := by linarith
  have hcarhalf := (polarCarrier_mono_radius (S₀ := S) (a := a) (b := b) hhalf).trans hcarrier
  have hcarann := (polarCarrier_mono_inner (R := R) (a := a) (b := b) hSR).trans hcarrier
  change domainPhaseCount v U (R / 2) a b R / R = _
  rw [domainPhaseCount_eq_phaseCount hv hcarann,
    domainPhaseCount_eq_phaseCount hv hcarrier,
    domainPhaseCount_eq_phaseCount hv hcarhalf,
    phaseCount_inner_split hS hSR hhalf (hv.mono hcarrier)]
  ring

#print axioms normalizedDivisorMeasure_real_dilation
#print axioms dilation_clippedSector
#print axioms normalizedDivisorMeasure_real_annulus
end V10.ScaledDivisorCount
