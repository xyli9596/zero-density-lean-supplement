import ZeroDensity.CountGeometry
import Mathlib.Topology.Order.Basic

/-! Open/closed angular count comparison for the actual disk-truncated
analytic divisor. Limits in this module are conditional comparison results. -/
noncomputable section
set_option autoImplicit false
open Filter Set
open scoped Topology
namespace ZeroDensity.SectorBounds
open ZeroDensity.CountGeometry

theorem open_closed_count_bounds {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (ψ : ℂ → ℂ) {S₀ a b c d r : ℝ} (hca : c < a) (hbd : b < d) :
    count f (pullback ψ S₀ a b) r ≤ count f (closedPullback ψ S₀ a b) r ∧
    count f (closedPullback ψ S₀ a b) r ≤ count f (pullback ψ S₀ c d) r := by
  exact ⟨count_mono r hf (pullback_subset_closed ψ S₀ a b),
    count_mono r hf (closedPullback_subset ψ hca hbd)⟩

/-- A closed sector has the same normalized density when it is squeezed
between its open sector and a buffered open sector of that density. -/
theorem closed_density_of_buffer {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (ψ : ℂ → ℂ) {S₀ a b c d L : ℝ} (hca : c < a) (hbd : b < d)
    (hsmall : Tendsto (fun r : ℝ => count f (pullback ψ S₀ a b) r / r)
      atTop (𝓝 L))
    (hlarge : Tendsto (fun r : ℝ => count f (pullback ψ S₀ c d) r / r)
      atTop (𝓝 L)) :
    Tendsto (fun r : ℝ => count f (closedPullback ψ S₀ a b) r / r)
      atTop (𝓝 L) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hsmall hlarge
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact div_le_div_of_nonneg_right (open_closed_count_bounds hf ψ hca hbd).1 hr.le
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact div_le_div_of_nonneg_right (open_closed_count_bounds hf ψ hca hbd).2 hr.le

#print axioms open_closed_count_bounds
#print axioms closed_density_of_buffer
end ZeroDensity.SectorBounds
