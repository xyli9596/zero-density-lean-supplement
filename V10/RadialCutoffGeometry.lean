import ZeroDensity.SectorDivisorCount
import Mathlib.Tactic

/-!
# Geometric radial cutoffs for v10 Lemma 3.4

These are actual inclusions of complex-plane sets, with no assumed count
sandwich. Strict radial increase permits a weak outer boundary inequality;
nondecreasing radial modulus instead requires a strict outer inequality.
The fixed inner annulus is retained explicitly. Conformality and divisor
multiplicity preservation are separate inputs to the subsequent count step.
-/

noncomputable section
open Set Metric
open ZeroDensity

namespace V10.RadialCutoffGeometry

abbrev rayPoint (ρ θ : ℝ) : ℂ :=
  (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

/-- The actual open-sided phase sector with a closed outer cutoff. -/
def clippedSector (S R a b : ℝ) : Set ℂ :=
  CountGeometry.angularSector S a b ∩ SectorDivisorCount.polarCarrier S R a b

/-- The physical image sector cut off by a closed disk. -/
def imageDisk (χ : ℂ → ℂ) (S a b r : ℝ) : Set ℂ :=
  CountGeometry.pullback χ S a b ∩ closedBall (0 : ℂ) r

lemma clippedSector_eq_norm {S R a b : ℝ} (hS : 0 ≤ S) :
    clippedSector S R a b =
      CountGeometry.angularSector S a b ∩ {s | ‖s‖ ≤ R} := by
  ext s
  constructor
  · rintro ⟨hs, hc⟩
    exact ⟨hs, (SectorDivisorCount.carrier_norm_bounds hS hc).2⟩
  · rintro ⟨hs, hn⟩
    exact ⟨hs, SectorDivisorCount.sector_carrier_of_norm_le hS hs hn⟩

/-- A nondecreasing radial modulus and the inner cutoff inequality put the
entire clipped sector image inside the physical disk. -/
theorem clipped_image_subset_closedBall
    (χ : ℂ → ℂ) {S R a b r : ℝ} (hS : 0 ≤ S) (hSR : S ≤ R)
    (hmono : ∀ θ ∈ Ioo a b, MonotoneOn (fun ρ => ‖χ (rayPoint ρ θ)‖) (Ici S))
    (hcut : ∀ θ ∈ Ioo a b, ‖χ (rayPoint R θ)‖ ≤ r) :
    χ '' clippedSector S R a b ⊆ closedBall (0 : ℂ) r := by
  rintro z ⟨s, hs, rfl⟩
  rw [clippedSector_eq_norm hS] at hs
  obtain ⟨ρ, hρ, θ, hθ, he⟩ := hs.1
  have hn : ‖s‖ = ρ := by
    rw [he, SectorDivisorCount.norm_polar (hS.trans hρ.le)]
  have hρR : ρ ≤ R := hn ▸ hs.2
  have hle := (hmono θ hθ) hρ.le hSR hρR
  rw [he]
  simpa only [mem_closedBall, dist_zero_right] using hle.trans (hcut θ hθ)

theorem clipped_image_subset_imageDisk
    (χ : ℂ → ℂ) {S₀ S R a b r : ℝ} (hS : 0 ≤ S) (hS₀S : S₀ ≤ S)
    (hSR : S ≤ R)
    (hmono : ∀ θ ∈ Ioo a b, MonotoneOn (fun ρ => ‖χ (rayPoint ρ θ)‖) (Ici S))
    (hcut : ∀ θ ∈ Ioo a b, ‖χ (rayPoint R θ)‖ ≤ r) :
    χ '' clippedSector S R a b ⊆ imageDisk χ S₀ a b r := by
  intro z hz
  refine ⟨?_, clipped_image_subset_closedBall χ hS hSR hmono hcut hz⟩
  obtain ⟨s, hs, he⟩ := hz
  exact ⟨s, SectorDivisorCount.angularSector_mono_inner hS₀S hs.1, he⟩

/-- Weak outer boundary comparison is sufficient when radial increase is
strict. This version retains zeros on the outer circle. -/
theorem imageDisk_subset_clipped_image_of_strictMono
    (χ : ℂ → ℂ) {S T a b r : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hmono : ∀ θ ∈ Ioo a b, StrictMonoOn (fun ρ => ‖χ (rayPoint ρ θ)‖) (Ici S))
    (hcut : ∀ θ ∈ Ioo a b, r ≤ ‖χ (rayPoint T θ)‖) :
    imageDisk χ S a b r ⊆ χ '' clippedSector S T a b := by
  rintro z ⟨⟨s, hs, he⟩, hz⟩
  obtain ⟨ρ, hρ, θ, hθ, hsray⟩ := hs
  have hnorm : ‖χ (rayPoint ρ θ)‖ ≤ r := by
    have : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    simpa only [← he, hsray] using this
  have hρT : ρ ≤ T := by
    by_contra h
    have hgt := (hmono θ hθ) hST hρ.le (lt_of_not_ge h)
    exact (not_lt_of_ge (hnorm.trans (hcut θ hθ))) hgt
  refine ⟨s, ?_, he⟩
  rw [clippedSector_eq_norm hS]
  refine ⟨⟨ρ, hρ, θ, hθ, hsray⟩, ?_⟩
  change ‖s‖ ≤ T
  rw [hsray, SectorDivisorCount.norm_polar (hS.trans hρ.le)]
  exact hρT

/-- With a strict outer inequality, a nondecreasing modulus already suffices. -/
theorem imageDisk_subset_clipped_image
    (χ : ℂ → ℂ) {S T a b r : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hmono : ∀ θ ∈ Ioo a b, MonotoneOn (fun ρ => ‖χ (rayPoint ρ θ)‖) (Ici S))
    (hcut : ∀ θ ∈ Ioo a b, r < ‖χ (rayPoint T θ)‖) :
    imageDisk χ S a b r ⊆ χ '' clippedSector S T a b := by
  rintro z ⟨⟨s, hs, he⟩, hz⟩
  obtain ⟨ρ, hρ, θ, hθ, hsray⟩ := hs
  have hnorm : ‖χ (rayPoint ρ θ)‖ ≤ r := by
    have : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    simpa only [← he, hsray] using this
  have hρT : ρ ≤ T := by
    by_contra h
    have hle := (hmono θ hθ) hST hρ.le (le_of_not_ge h)
    exact (not_lt_of_ge (hle.trans hnorm)) (hcut θ hθ)
  refine ⟨s, ?_, he⟩
  rw [clippedSector_eq_norm hS]
  refine ⟨⟨ρ, hρ, θ, hθ, hsray⟩, ?_⟩
  change ‖s‖ ≤ T
  rw [hsray, SectorDivisorCount.norm_polar (hS.trans hρ.le)]
  exact hρT

/-- Raising the inner cutoff discards only the image of one fixed compact
polar carrier. This is purely geometric and requires no injectivity. -/
theorem pullback_subset_tail_union_inner
    (χ : ℂ → ℂ) {S₀ S₁ a b : ℝ} (hS₀ : 0 ≤ S₀) :
    CountGeometry.pullback χ S₀ a b ⊆
      CountGeometry.pullback χ S₁ a b ∪
        χ '' SectorDivisorCount.polarCarrier S₀ S₁ a b := by
  rintro z ⟨s, hs, he⟩
  by_cases hN : S₁ < ‖s‖
  · exact Or.inl ⟨s, SectorDivisorCount.sector_of_norm_gt hS₀ hs hN, he⟩
  · exact Or.inr ⟨s, SectorDivisorCount.sector_carrier_of_norm_le hS₀ hs
      (le_of_not_gt hN), he⟩

/-- The physical disk cutoff lies in the large phase cutoff image, up to
one fixed inner carrier. This supplies the geometric input for an actual
divisor-count upper bound, rather than assuming that count bound. -/
theorem imageDisk_subset_outer_union_inner
    (χ : ℂ → ℂ) {S₀ S₁ T a b r : ℝ} (hS₀ : 0 ≤ S₀) (hS₁ : 0 ≤ S₁)
    (hST : S₁ ≤ T)
    (hmono : ∀ θ ∈ Ioo a b, MonotoneOn (fun ρ => ‖χ (rayPoint ρ θ)‖) (Ici S₁))
    (hcut : ∀ θ ∈ Ioo a b, r < ‖χ (rayPoint T θ)‖) :
    imageDisk χ S₀ a b r ⊆ χ '' clippedSector S₁ T a b ∪
      χ '' SectorDivisorCount.polarCarrier S₀ S₁ a b := by
  intro z hz
  rcases pullback_subset_tail_union_inner χ hS₀ hz.1 with htail | hinner
  · exact Or.inl (imageDisk_subset_clipped_image χ hS₁ hST hmono hcut ⟨htail, hz.2⟩)
  · exact Or.inr hinner

#print axioms clipped_image_subset_imageDisk
#print axioms imageDisk_subset_clipped_image_of_strictMono
#print axioms imageDisk_subset_outer_union_inner

end V10.RadialCutoffGeometry
