import ZeroDensity.CountGeometry
import ZeroDensity.FiniteJumps
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Corollary 1.2, relative to the precise counting law of Theorem 1.1.

`CountingLaw` is explicitly a premise here. This module does not prove the
ODE-to-counting-law implication. Counts are actual analytic divisors.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Metric Asymptotics
open scoped Topology

namespace ZeroDensity.Corollary
open CountGeometry FiniteJumps

def scale (a β r : ℝ) : ℝ := r ^ β * Real.exp (a * r)

theorem scale_pos (a β : ℝ) {r : ℝ} (hr : 0 < r) : 0 < scale a β r :=
  mul_pos (Real.rpow_pos_of_pos hr β) (Real.exp_pos _)

/-- The counting formula with exactly its endpoint continuity conditions. -/
def CountingLaw (f ψ : ℂ → ℂ) (S₀ l u a β : ℝ) (M : ℝ → ℝ) : Prop :=
  ∀ α₁ α₂ : ℝ, l < α₁ → α₁ < α₂ → α₂ < u →
    ContinuousAt M α₁ → ContinuousAt M α₂ →
    Tendsto (fun r => count f (pullback ψ S₀ α₁ α₂) r / scale a β r)
      atTop (𝓝 (M α₂ - M α₁))

theorem zero_density_at_equal_endpoints {f ψ : ℂ → ℂ} {S₀ l u a β : ℝ}
    {M : ℝ → ℝ} (hlaw : CountingLaw f ψ S₀ l u a β M)
    {α₁ α₂ : ℝ} (hleft : l < α₁) (horder : α₁ < α₂) (hright : α₂ < u)
    (hc₁ : ContinuousAt M α₁) (hc₂ : ContinuousAt M α₂)
    (heq : M α₁ = M α₂) :
    (fun r => count f (pullback ψ S₀ α₁ α₂) r) =o[atTop] scale a β := by
  have hlim := hlaw α₁ α₂ hleft horder hright hc₁ hc₂
  rw [← heq, sub_self] at hlim
  apply (isLittleO_iff_tendsto' ?_).mpr hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact fun hz => False.elim ((ne_of_gt (scale_pos a β hr)) hz)

theorem zero_density_of_subset {f : ℂ → ℂ} {U V : Set ℂ} {a β : ℝ}
    (hf : Differentiable ℂ f) (hUV : U ⊆ V)
    (hV : (fun r => count f V r) =o[atTop] scale a β) :
    (fun r => count f U r) =o[atTop] scale a β := by
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [hV.bound hε] with r hr
  have hU0 := count_nonneg U r hf
  have hV0 := count_nonneg V r hf
  simpa only [Real.norm_eq_abs, abs_of_nonneg hU0, abs_of_nonneg hV0] using
    (count_mono r hf hUV).trans (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hV0] using hr)

/-- Complete endpoint-inclusive zero-density deduction, for a concrete finite
step density. The sole analytic input is Theorem 1.1's counting formula. -/
theorem zero_density_on_jump_free_interval {f ψ : ℂ → ℂ} {S₀ l u a β : ℝ}
    (hf : Differentiable ℂ f) (s : Finset ℝ) (w : ℝ → ℝ)
    (hlaw : CountingLaw f ψ S₀ l u a β (density s w))
    {α₁ α₂ : ℝ} (hleft : l < α₁) (horder : α₁ < α₂) (hright : α₂ < u)
    (hfree : ∀ η ∈ s, η ∉ Icc α₁ α₂) :
    (fun r => count f (closedPullback ψ S₀ α₁ α₂) r) =o[atTop] scale a β := by
  obtain ⟨δ₀, hδ₀, hbuffer⟩ := finite_buffer s horder.le hfree
  let δ := min δ₀ (min ((α₁ - l) / 2) ((u - α₂) / 2))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (by linarith) (by linarith))
  have hδ₀le : δ ≤ δ₀ := min_le_left _ _
  have hδleft : δ ≤ (α₁ - l) / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδright : δ ≤ (u - α₂) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hfree' : ∀ η ∈ s, η ∉ Icc (α₁ - δ) (α₂ + δ) := by
    intro η hη he
    exact hbuffer η hη ⟨by linarith [he.1], by linarith [he.2]⟩
  have horder' : α₁ - δ < α₂ + δ := by linarith
  have hc₁ : ContinuousAt (density s w) (α₁ - δ) := by
    apply density_continuousAt
    intro hmem
    exact hfree' _ hmem ⟨le_rfl, horder'.le⟩
  have hc₂ : ContinuousAt (density s w) (α₂ + δ) := by
    apply density_continuousAt
    intro hmem
    exact hfree' _ hmem ⟨horder'.le, le_rfl⟩
  have heq := density_eq_of_no_jumps s w horder'.le hfree'
  have houter := zero_density_at_equal_endpoints hlaw
    (by linarith : l < α₁ - δ) horder' (by linarith : α₂ + δ < u) hc₁ hc₂ heq
  exact zero_density_of_subset hf
    (closedPullback_subset ψ (by linarith : α₁ - δ < α₁)
      (by linarith : α₂ < α₂ + δ)) houter

theorem corollary_1_2 {f ψ : ℂ → ℂ} {S₀ l u a β : ℝ}
    (hf : Differentiable ℂ f) (_hne : f ≠ 0) (s : Finset ℝ) (w : ℝ → ℝ)
    (hlaw : CountingLaw f ψ S₀ l u a β (density s w))
    {α₁ α₂ : ℝ} (hleft : l < α₁) (horder : α₁ < α₂) (hright : α₂ < u)
    (hfree : ∀ θ ∈ Icc α₁ α₂, ContinuousAt (density s w) θ) :
    (fun r => count f (closedPullback ψ S₀ α₁ α₂) r) =o[atTop] scale a β := by
  have heq : density (activeJumps s w) w = density s w := by
    funext θ
    exact density_activeJumps s w θ
  have hlaw' : CountingLaw f ψ S₀ l u a β (density (activeJumps s w) w) := by
    rw [heq]
    exact hlaw
  apply zero_density_on_jump_free_interval hf (activeJumps s w) w hlaw'
    hleft horder hright
  intro η hη hint
  exact ((density_continuousAt_iff s w η).mp (hfree η hint)) hη

theorem corollary_1_2_open {f ψ : ℂ → ℂ} {S₀ l u a β : ℝ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) (s : Finset ℝ) (w : ℝ → ℝ)
    (hlaw : CountingLaw f ψ S₀ l u a β (density s w))
    {α₁ α₂ : ℝ} (hleft : l < α₁) (horder : α₁ < α₂) (hright : α₂ < u)
    (hfree : ∀ θ ∈ Icc α₁ α₂, ContinuousAt (density s w) θ) :
    (fun r => count f (pullback ψ S₀ α₁ α₂) r) =o[atTop] scale a β :=
  zero_density_of_subset hf (pullback_subset_closed ψ S₀ α₁ α₂)
    (corollary_1_2 hf hne s w hlaw hleft horder hright hfree)

#print axioms scale_pos
#print axioms zero_density_at_equal_endpoints
#print axioms zero_density_of_subset
#print axioms zero_density_on_jump_free_interval
#print axioms corollary_1_2
#print axioms corollary_1_2_open

end ZeroDensity.Corollary
