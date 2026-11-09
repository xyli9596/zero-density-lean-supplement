import CRGZeroDistributionScaled
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Actual zero multiplicities in bounded subsets and angular pullbacks.
The counting domains need not be closed. They are cut off by a compact disk.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeromorphicOn
open scoped Topology

namespace ZeroDensity.CountGeometry

attribute [local instance] Classical.propDecidable

def count (f : ℂ → ℂ) (U : Set ℂ) (r : ℝ) : ℝ :=
  ((∑ᶠ z, if z ∈ U then
    MeromorphicOn.divisor f (closedBall (0 : ℂ) r) z else 0 : ℤ) : ℝ)

def angularSector (S₀ a b : ℝ) : Set ℂ :=
  {s | ∃ R : ℝ, S₀ < R ∧ ∃ θ : ℝ, θ ∈ Ioo a b ∧
    s = (R : ℂ) * Complex.exp (θ * Complex.I)}

def pullback (ψ : ℂ → ℂ) (S₀ a b : ℝ) : Set ℂ :=
  ψ '' angularSector S₀ a b

def closedAngularSector (S₀ a b : ℝ) : Set ℂ :=
  {s | ∃ R : ℝ, S₀ < R ∧ ∃ θ : ℝ, θ ∈ Icc a b ∧
    s = (R : ℂ) * Complex.exp (θ * Complex.I)}

def closedPullback (ψ : ℂ → ℂ) (S₀ a b : ℝ) : Set ℂ :=
  ψ '' closedAngularSector S₀ a b

theorem filtered_support_finite (f : ℂ → ℂ) (U : Set ℂ) (r : ℝ) :
    (Function.support (fun z => if z ∈ U then
      MeromorphicOn.divisor f (closedBall (0 : ℂ) r) z else 0)).Finite := by
  classical
  apply ((MeromorphicOn.divisor f (closedBall (0 : ℂ) r)).finiteSupport
    (isCompact_closedBall (0 : ℂ) r)).subset
  intro z hz
  by_cases h : z ∈ U
  · simpa [h, Function.mem_support] using hz
  · simp [h, Function.mem_support] at hz

theorem count_nonneg {f : ℂ → ℂ} (U : Set ℂ) (r : ℝ)
    (hf : Differentiable ℂ f) : 0 ≤ count f U r := by
  classical
  have ha : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono (subset_univ _)
  unfold count
  exact_mod_cast (finsum_nonneg (fun z => by
    split_ifs
    · exact ha.divisor_nonneg z
    · exact le_rfl))

theorem count_mono {f : ℂ → ℂ} {U V : Set ℂ} (r : ℝ)
    (hf : Differentiable ℂ f) (hUV : U ⊆ V) : count f U r ≤ count f V r := by
  classical
  have ha : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono (subset_univ _)
  have hle : ∀ z, (if z ∈ U then MeromorphicOn.divisor f (closedBall (0 : ℂ) r) z else 0) ≤
      (if z ∈ V then MeromorphicOn.divisor f (closedBall (0 : ℂ) r) z else 0) := by
    intro z
    by_cases hU : z ∈ U
    · simp [hU, hUV hU]
    · simp only [hU, ↓reduceIte]
      split_ifs
      · exact ha.divisor_nonneg z
      · exact le_rfl
  have h := finsum_le_finsum' (filtered_support_finite f U r)
    (filtered_support_finite f V r) hle
  unfold count
  exact_mod_cast h

theorem angularSector_mono {S₀ a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    angularSector S₀ a b ⊆ angularSector S₀ c d := by
  rintro s ⟨R, hR, θ, hθ, hs⟩
  exact ⟨R, hR, θ, ⟨lt_of_le_of_lt hca hθ.1, lt_of_lt_of_le hθ.2 hbd⟩, hs⟩

theorem pullback_mono (ψ : ℂ → ℂ) {S₀ a b c d : ℝ}
    (hca : c ≤ a) (hbd : b ≤ d) : pullback ψ S₀ a b ⊆ pullback ψ S₀ c d :=
  image_mono (angularSector_mono hca hbd)

theorem closedPullback_subset (ψ : ℂ → ℂ) {S₀ a b c d : ℝ}
    (hca : c < a) (hbd : b < d) : closedPullback ψ S₀ a b ⊆ pullback ψ S₀ c d := by
  apply image_mono
  rintro s ⟨R, hR, θ, hθ, hs⟩
  exact ⟨R, hR, θ, ⟨lt_of_lt_of_le hca hθ.1, lt_of_le_of_lt hθ.2 hbd⟩, hs⟩

theorem pullback_subset_closed (ψ : ℂ → ℂ) (S₀ a b : ℝ) :
    pullback ψ S₀ a b ⊆ closedPullback ψ S₀ a b := by
  apply image_mono
  rintro s ⟨R, hR, θ, hθ, hs⟩
  exact ⟨R, hR, θ, ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩, hs⟩

#print axioms filtered_support_finite
#print axioms count_nonneg
#print axioms count_mono
#print axioms angularSector_mono
#print axioms pullback_mono
#print axioms closedPullback_subset
#print axioms pullback_subset_closed

end ZeroDensity.CountGeometry
