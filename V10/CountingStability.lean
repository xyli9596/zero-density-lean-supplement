import ZeroDensity.CountGeometry
import V10.ExponentialScales

/-!
# Stability of actual zero counts under changes of region

This module uses the actual analytic divisor, including multiplicities,
and the very same disk-truncated count as the legacy project.
It proves the second assertion of v10 Corollary 7.2 from its first
assertion. The ODE estimate for the discarded region is still a separate
obligation; it is not hidden in the definition of a solution.
-/

noncomputable section
open Set Filter Metric MeromorphicOn
open scoped Topology symmDiff

namespace V10.CountingStability
open ZeroDensity.CountGeometry V10.ExponentialScales

theorem count_union_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (U V : Set ℂ) (r : ℝ) :
    count f (U ∪ V) r ≤ count f U r + count f V r := by
  classical
  have ha : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).mono (subset_univ _)
  have hU := filtered_support_finite f U r
  have hV := filtered_support_finite f V r
  have hi := finsum_le_finsum' (filtered_support_finite f (U ∪ V) r)
    (Function.HasFiniteSupport.add hU hV) (fun z => by
      have hn : 0 ≤ divisor f (closedBall (0 : ℂ) r) z := ha.divisor_nonneg z
      by_cases hu : z ∈ U <;> by_cases hv : z ∈ V <;> simp [Pi.add_apply, hu, hv, hn])
  simp only [Pi.add_apply] at hi
  rw [finsum_add_distrib hU hV] at hi
  unfold count
  exact_mod_cast hi

theorem count_le_add_of_subset_union {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U V X : Set ℂ} (hU : U ⊆ V ∪ X) (r : ℝ) :
    count f U r ≤ count f V r + count f X r :=
  (count_mono r hf hU).trans (count_union_le hf V X r)

/-- Moving any zero across a changed boundary changes the count by at most
    its multiplicity; no regularity of the boundaries is required. -/
theorem abs_count_sub_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U V X : Set ℂ} (hUV : U ∆ V ⊆ X) (r : ℝ) :
    |count f V r - count f U r| ≤ count f X r := by
  have hU : U ⊆ V ∪ X := by
    intro z hz
    by_cases hv : z ∈ V
    · exact Or.inl hv
    · exact Or.inr (hUV (Or.inl ⟨hz, hv⟩))
  have hV : V ⊆ U ∪ X := by
    intro z hz
    by_cases hu : z ∈ U
    · exact Or.inl hu
    · exact Or.inr (hUV (Or.inr ⟨hz, hu⟩))
  have h1 := count_le_add_of_subset_union hf hU r
  have h2 := count_le_add_of_subset_union hf hV r
  rw [abs_le]
  constructor <;> linarith

/-- Corollary 7.2's stability conclusion, with actual zero counts and with
    the discarded-region estimate explicitly retained as a hypothesis. -/
theorem counting_stability {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U V X : Set ℂ} (hUV : U ∆ V ⊆ X) {a b C N : ℝ}
    (hba : b < a)
    (hX : ∀ᶠ r in atTop, count f X r ≤ C * scale b N r)
    (η : ℝ) :
    (fun r => count f V r - count f U r) =o[atTop] scale a η := by
  apply negligible_of_exp_bound hba
  filter_upwards [hX] with r hr
  exact (abs_count_sub_le hf hUV r).trans hr

/-- The principal coefficient is preserved, including the zero-coefficient
    version which is useful before positivity has been established. -/
theorem principal_coefficient_preserved {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U V X : Set ℂ} (hUV : U ∆ V ⊆ X) {a b C N β c : ℝ}
    (hba : b < a)
    (hX : ∀ᶠ r in atTop, count f X r ≤ C * scale b N r)
    (hU : Tendsto (fun r => count f U r / scale a β r) atTop (𝓝 c)) :
    Tendsto (fun r => count f V r / scale a β r) atTop (𝓝 c) := by
  have hd := (counting_stability hf hUV hba hX β).tendsto_div_nhds_zero
  have ht := hd.add hU
  simpa only [sub_div, sub_add_cancel, zero_add] using ht

end V10.CountingStability
