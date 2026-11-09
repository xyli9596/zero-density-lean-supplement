import ZeroDensity.CountGeometry
import ZeroDensity.ConformalMultiplicity
import Mathlib.Topology.Instances.RealVectorSpace

/-! Actual phase-sector divisor counts on compact polar carriers. Unlike an
entire-function disk count, these definitions only need analyticity near the
closed truncated sector where the phase solution is defined. -/
namespace ZeroDensity.SectorDivisorCount
open Set Filter Metric MeromorphicOn
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def polarMap (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)

def polarCarrier (S₀ R a b : ℝ) : Set ℂ :=
  polarMap '' (Icc S₀ R ×ˢ Icc a b)

lemma mem_polarCarrier {s : ℂ} {S₀ R a b : ℝ} :
    s ∈ polarCarrier S₀ R a b ↔ ∃ r ∈ Icc S₀ R, ∃ θ ∈ Icc a b,
      s = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  constructor
  · rintro ⟨⟨r, θ⟩, ⟨hr, hθ⟩, hs⟩
    exact ⟨r, hr, θ, hθ, hs.symm⟩
  · rintro ⟨r, hr, θ, hθ, hs⟩
    exact ⟨(r, θ), ⟨hr, hθ⟩, hs.symm⟩

lemma polarCarrier_compact (S₀ R a b : ℝ) : IsCompact (polarCarrier S₀ R a b) := by
  apply (isCompact_Icc.prod isCompact_Icc).image
  unfold polarMap
  fun_prop

lemma polarCarrier_mono_radius {S₀ R T a b : ℝ} (hRT : R ≤ T) :
    polarCarrier S₀ R a b ⊆ polarCarrier S₀ T a b := by
  apply image_mono
  exact prod_mono (Icc_subset_Icc le_rfl hRT) subset_rfl

lemma polarCarrier_mono_inner {S₀ S₁ R a b : ℝ} (hS : S₀ ≤ S₁) :
    polarCarrier S₁ R a b ⊆ polarCarrier S₀ R a b := by
  apply image_mono
  exact prod_mono (Icc_subset_Icc hS le_rfl) subset_rfl

/-- Actual zero count with an open inner cutoff and open angular sides; the
outer radial boundary is included. The compact carrier supplies finite support. -/
def phaseCount (v : ℂ → ℂ) (S₀ a b R : ℝ) : ℝ :=
  ((∑ᶠ s, if s ∈ CountGeometry.angularSector S₀ a b then
    divisor v (polarCarrier S₀ R a b) s else 0 : ℤ) : ℝ)

lemma filtered_support_finite (v : ℂ → ℂ) (S₀ a b R : ℝ) :
    (Function.support (fun s => if s ∈ CountGeometry.angularSector S₀ a b then
      divisor v (polarCarrier S₀ R a b) s else 0)).Finite := by
  apply ((divisor v (polarCarrier S₀ R a b)).finiteSupport
    (polarCarrier_compact S₀ R a b)).subset
  intro s hs
  by_cases h : s ∈ CountGeometry.angularSector S₀ a b
  · simpa [h, Function.mem_support] using hs
  · simp [h, Function.mem_support] at hs

/-- Divisors on overlapping analytic domains agree because they evaluate the
same actual analytic germ order, independently of the chosen compact carrier. -/
lemma divisor_domains_eq {v : ℂ → ℂ} {U V : Set ℂ} {s : ℂ}
    (hU : AnalyticOnNhd ℂ v U) (hV : AnalyticOnNhd ℂ v V)
    (hsU : s ∈ U) (hsV : s ∈ V) : divisor v U s = divisor v V s := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hU hsU,
    MeromorphicOn.AnalyticOnNhd.divisor_apply hV hsV]

lemma divisor_zero_outside {v : ℂ → ℂ} {U : Set ℂ} {s : ℂ} (hs : s ∉ U) :
    divisor v U s = 0 := by
  simp [hs]

theorem phaseCount_nonneg {v : ℂ → ℂ} {S₀ a b R : ℝ}
    (hv : AnalyticOnNhd ℂ v (polarCarrier S₀ R a b)) :
    0 ≤ phaseCount v S₀ a b R := by
  unfold phaseCount
  exact_mod_cast (finsum_nonneg (fun s => by
    split_ifs
    · exact hv.divisor_nonneg s
    · exact le_rfl))

theorem phaseCount_mono_radius {v : ℂ → ℂ} {S₀ a b R T : ℝ} (hRT : R ≤ T)
    (hv : AnalyticOnNhd ℂ v (polarCarrier S₀ T a b)) :
    phaseCount v S₀ a b R ≤ phaseCount v S₀ a b T := by
  have hsub := polarCarrier_mono_radius (S₀ := S₀) (a := a) (b := b) hRT
  have hsmall := hv.mono hsub
  have hle : ∀ s, (if s ∈ CountGeometry.angularSector S₀ a b then
      divisor v (polarCarrier S₀ R a b) s else 0) ≤
      (if s ∈ CountGeometry.angularSector S₀ a b then
      divisor v (polarCarrier S₀ T a b) s else 0) := by
    intro s
    split_ifs with hs
    · by_cases hc : s ∈ polarCarrier S₀ R a b
      · rw [divisor_domains_eq hsmall hv hc (hsub hc)]
      · rw [divisor_zero_outside hc]
        exact hv.divisor_nonneg s
    · exact le_rfl
  have hi := finsum_le_finsum' (filtered_support_finite v S₀ a b R)
    (filtered_support_finite v S₀ a b T) hle
  unfold phaseCount
  exact_mod_cast hi

lemma norm_polar {r θ : ℝ} (hr : 0 ≤ r) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, abs_of_nonneg hr]

lemma carrier_norm_bounds {s : ℂ} {S₀ R a b : ℝ} (hS : 0 ≤ S₀)
    (hs : s ∈ polarCarrier S₀ R a b) : S₀ ≤ ‖s‖ ∧ ‖s‖ ≤ R := by
  obtain ⟨r, hr, θ, hθ, he⟩ := mem_polarCarrier.mp hs
  rw [he, norm_polar (hS.trans hr.1)]
  exact hr

lemma angularSector_mono_inner {S₀ S₁ a b : ℝ} (hS : S₀ ≤ S₁) :
    CountGeometry.angularSector S₁ a b ⊆ CountGeometry.angularSector S₀ a b := by
  rintro s ⟨r, hr, θ, hθ, he⟩
  exact ⟨r, hS.trans_lt hr, θ, hθ, he⟩

lemma sector_norm_gt {s : ℂ} {S₀ a b : ℝ} (hS : 0 ≤ S₀)
    (hs : s ∈ CountGeometry.angularSector S₀ a b) : S₀ < ‖s‖ := by
  obtain ⟨r, hr, θ, hθ, he⟩ := hs
  rw [he, norm_polar (hS.trans hr.le)]
  exact hr

lemma sector_carrier_of_norm_le {s : ℂ} {S₀ R a b : ℝ} (hS : 0 ≤ S₀)
    (hs : s ∈ CountGeometry.angularSector S₀ a b) (hR : ‖s‖ ≤ R) :
    s ∈ polarCarrier S₀ R a b := by
  obtain ⟨r, hr, θ, hθ, he⟩ := hs
  have hn : ‖s‖ = r := by rw [he, norm_polar (hS.trans hr.le)]
  exact mem_polarCarrier.mpr ⟨r, ⟨hr.le, hn ▸ hR⟩, θ, ⟨hθ.1.le, hθ.2.le⟩, he⟩

lemma sector_of_norm_gt {s : ℂ} {S₀ S₁ a b : ℝ} (hS : 0 ≤ S₀)
    (hs : s ∈ CountGeometry.angularSector S₀ a b) (hN : S₁ < ‖s‖) :
    s ∈ CountGeometry.angularSector S₁ a b := by
  obtain ⟨r, hr, θ, hθ, he⟩ := hs
  have hn : ‖s‖ = r := by rw [he, norm_polar (hS.trans hr.le)]
  exact ⟨r, hn ▸ hN, θ, hθ, he⟩

lemma carrier_of_norm_ge_inner {s : ℂ} {S₀ S₁ R a b : ℝ} (hS : 0 ≤ S₀)
    (hs : s ∈ polarCarrier S₀ R a b) (hN : S₁ ≤ ‖s‖) :
    s ∈ polarCarrier S₁ R a b := by
  obtain ⟨r, hr, θ, hθ, he⟩ := mem_polarCarrier.mp hs
  have hn : ‖s‖ = r := by rw [he, norm_polar (hS.trans hr.1)]
  exact mem_polarCarrier.mpr ⟨r, ⟨hn ▸ hN, hr.2⟩, θ, hθ, he⟩

/-- Raising the inner cutoff removes exactly the actual finite inner-sector
count, including zeros on the new inner radial boundary. -/
theorem phaseCount_inner_split {v : ℂ → ℂ} {S₀ S₁ R a b : ℝ}
    (hS0 : 0 ≤ S₀) (hS : S₀ ≤ S₁) (hR : S₁ ≤ R)
    (hv : AnalyticOnNhd ℂ v (polarCarrier S₀ R a b)) :
    phaseCount v S₀ a b R = phaseCount v S₁ a b R + phaseCount v S₀ a b S₁ := by
  have hsub1 := polarCarrier_mono_inner (R := R) (a := a) (b := b) hS
  have hsub0 := polarCarrier_mono_radius (S₀ := S₀) (a := a) (b := b) hR
  have hv1 := hv.mono hsub1
  have hv0 := hv.mono hsub0
  have heq : (fun s => if s ∈ CountGeometry.angularSector S₀ a b then
      divisor v (polarCarrier S₀ R a b) s else 0) =
      (fun s => if s ∈ CountGeometry.angularSector S₁ a b then
        divisor v (polarCarrier S₁ R a b) s else 0) +
      (fun s => if s ∈ CountGeometry.angularSector S₀ a b then
        divisor v (polarCarrier S₀ S₁ a b) s else 0) := by
    funext s
    simp only [Pi.add_apply]
    by_cases hs : s ∈ CountGeometry.angularSector S₀ a b
    · by_cases hn : S₁ < ‖s‖
      · have hs1 := sector_of_norm_gt hS0 hs hn
        have hn0 : s ∉ polarCarrier S₀ S₁ a b := by
          intro hc
          exact (not_le_of_gt hn) (carrier_norm_bounds hS0 hc).2
        simp only [if_pos hs, if_pos hs1, divisor_zero_outside hn0, add_zero]
        by_cases hc : s ∈ polarCarrier S₀ R a b
        · have hc1 := carrier_of_norm_ge_inner hS0 hc hn.le
          exact divisor_domains_eq hv hv1 hc hc1
        · have hc1 : s ∉ polarCarrier S₁ R a b := fun hm => hc (hsub1 hm)
          rw [divisor_zero_outside hc, divisor_zero_outside hc1]
      · have hn' : ‖s‖ ≤ S₁ := le_of_not_gt hn
        have hs1 : s ∉ CountGeometry.angularSector S₁ a b := by
          intro hm
          exact (not_lt_of_ge hn') (sector_norm_gt (hS0.trans hS) hm)
        have hc0 := sector_carrier_of_norm_le hS0 hs hn'
        have hc := hsub0 hc0
        simp only [if_pos hs, if_neg hs1, zero_add]
        exact divisor_domains_eq hv hv0 hc hc0
    · have hs1 : s ∉ CountGeometry.angularSector S₁ a b :=
        fun hm => hs (angularSector_mono_inner hS hm)
      simp [hs, hs1]
  have hi := congrArg (fun f : ℂ → ℤ => ∑ᶠ s, f s) heq
  simp only [Pi.add_apply] at hi
  rw [finsum_add_distrib (filtered_support_finite v S₁ a b R)
    (filtered_support_finite v S₀ a b S₁)] at hi
  unfold phaseCount
  exact_mod_cast hi

/-- The inner-cutoff error is uniformly bounded by a fixed, actual compact
annulus count. Analyticity is needed only on the relevant compact carriers. -/
theorem phaseCount_inner_error {v : ℂ → ℂ} {S₀ S₁ R a b : ℝ}
    (hS0 : 0 ≤ S₀) (hS : S₀ ≤ S₁) (hR : S₁ ≤ R)
    (hv : AnalyticOnNhd ℂ v (polarCarrier S₀ R a b)) :
    |phaseCount v S₀ a b R - phaseCount v S₁ a b R| = phaseCount v S₀ a b S₁ := by
  rw [phaseCount_inner_split hS0 hS hR hv]
  have hn := phaseCount_nonneg (hv.mono (polarCarrier_mono_radius hR))
  simpa using abs_of_nonneg hn

/-- Counting on a larger analytic domain gives exactly the same actual count,
provided the geometric compact carrier is retained as the cutoff. -/
theorem phaseCount_eq_domain {v : ℂ → ℂ} {U : Set ℂ} {S₀ R a b : ℝ}
    (hv : AnalyticOnNhd ℂ v U) (hsub : polarCarrier S₀ R a b ⊆ U) :
    phaseCount v S₀ a b R =
      ((∑ᶠ s, if s ∈ CountGeometry.angularSector S₀ a b ∧ s ∈ polarCarrier S₀ R a b
        then divisor v U s else 0 : ℤ) : ℝ) := by
  unfold phaseCount
  congr 1
  apply finsum_congr
  intro s
  by_cases ha : s ∈ CountGeometry.angularSector S₀ a b
  · by_cases hc : s ∈ polarCarrier S₀ R a b
    · simp only [ha, hc, true_and, ite_true]
      exact divisor_domains_eq (hv.mono hsub) hv hc (hsub hc)
    · simp [ha, hc, divisor_zero_outside hc]
  · simp [ha]

lemma polarCarrier_subset_wider_sector {Sbase S₀ R a0 a b b0 : ℝ}
    (hS : Sbase < S₀) (ha : a0 < a) (hb : b < b0) :
    polarCarrier S₀ R a b ⊆ CountGeometry.angularSector Sbase a0 b0 := by
  intro s hs
  obtain ⟨r, hr, θ, hθ, he⟩ := mem_polarCarrier.mp hs
  exact ⟨r, hS.trans_le hr.1, θ,
    ⟨ha.trans_le hθ.1, hθ.2.trans_lt hb⟩, he⟩

/-- On a wider phase sector the finite inner-annulus error is one fixed
constant for all outer radii, without entire analyticity of the phase solution. -/
theorem inner_error_bounded_on_sector {v : ℂ → ℂ} {Sbase S₀ S₁ a0 a b b0 : ℝ}
    (hS0 : 0 ≤ S₀) (hS : S₀ ≤ S₁) (hbase : Sbase < S₀)
    (ha : a0 < a) (hb : b < b0)
    (hv : AnalyticOnNhd ℂ v (CountGeometry.angularSector Sbase a0 b0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R ≥ S₁,
      |phaseCount v S₀ a b R - phaseCount v S₁ a b R| ≤ C := by
  refine ⟨phaseCount v S₀ a b S₁, ?_, ?_⟩
  · exact phaseCount_nonneg (hv.mono (polarCarrier_subset_wider_sector hbase ha hb))
  · intro R hR
    exact (phaseCount_inner_error hS0 hS hR
      (hv.mono (polarCarrier_subset_wider_sector hbase ha hb))).le

#print axioms polarCarrier_compact
#print axioms phaseCount_nonneg
#print axioms phaseCount_mono_radius
#print axioms phaseCount_inner_split
#print axioms phaseCount_inner_error
#print axioms phaseCount_eq_domain
#print axioms inner_error_bounded_on_sector

end
end ZeroDensity.SectorDivisorCount
