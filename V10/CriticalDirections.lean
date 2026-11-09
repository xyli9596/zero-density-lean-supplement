import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# The strict geometric gap at a critical direction

This is the finite-dimensional geometric input to Proposition 7.1.
If two distinct frequencies in the closed disk of radius `a` tie in
one unit direction, their common real projection is strictly below `a`.
The uniform gap over finitely many critical directions is proved too.
The analytic zero-count estimate on the associated neighborhoods is
not asserted here.
-/

noncomputable section
namespace V10.CriticalDirections

theorem eq_of_re_eq_radius {z : ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hz : ‖z‖ ≤ a) (hre : z.re = a) : z = (a : ℂ) := by
  have habs : |z.re| = ‖z‖ := by
    rw [hre, abs_of_nonneg ha]
    exact le_antisymm (hre ▸ Complex.re_le_norm z) hz
  have him := Complex.abs_re_eq_norm.mp habs
  apply Complex.ext <;> simp [hre, him]

theorem tied_projection_lt {ω ν d : ℂ} {a : ℝ}
    (ha : 0 < a) (hω : ‖ω‖ ≤ a) (hν : ‖ν‖ ≤ a)
    (hd : ‖d‖ = 1) (hne : ω ≠ ν)
    (htie : (ω * d).re = (ν * d).re) : (ω * d).re < a := by
  have hωd : ‖ω * d‖ ≤ a := by simpa [norm_mul, hd] using hω
  have hνd : ‖ν * d‖ ≤ a := by simpa [norm_mul, hd] using hν
  apply lt_of_le_of_ne ((Complex.re_le_norm _).trans hωd)
  intro heq
  have h1 := eq_of_re_eq_radius ha.le hωd heq
  have h2 := eq_of_re_eq_radius ha.le hνd (htie.symm.trans heq)
  have hd0 : d ≠ 0 := by intro h; simp [h] at hd
  exact hne (mul_right_cancel₀ hd0 (h1.trans h2.symm))

/-- This formulation allows the zero frequency as a competing point,
    just as the convex hull in the paper includes the origin. -/
theorem max_zero_tied_projection_lt {ω ν d : ℂ} {a : ℝ}
    (ha : 0 < a) (hω : ‖ω‖ ≤ a) (hν : ‖ν‖ ≤ a)
    (hd : ‖d‖ = 1) (hne : ω ≠ ν)
    (htie : (ω * d).re = (ν * d).re) : max 0 (ω * d).re < a :=
  max_lt ha (tied_projection_lt ha hω hν hd hne htie)

theorem finite_uniform_gap {ι : Type*} (s : Finset ι) (H : ι → ℝ)
    {a : ℝ} (ha : 0 < a) (hH : ∀ i ∈ s, H i < a) :
    ∃ b : ℝ, 0 ≤ b ∧ b < a ∧ ∀ i ∈ s, H i ≤ b := by
  classical
  by_cases hs : s.Nonempty
  · refine ⟨max 0 (s.sup' hs H), le_max_left _ _, ?_, ?_⟩
    · exact max_lt ha ((Finset.sup'_lt_iff hs).mpr hH)
    · intro i hi
      exact (Finset.le_sup' H hi).trans (le_max_right _ _)
  · refine ⟨0, le_rfl, ha, ?_⟩
    intro i hi
    exact (hs ⟨i, hi⟩).elim

end V10.CriticalDirections
