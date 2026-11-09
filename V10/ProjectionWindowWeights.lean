import V10.SmoothMeasureMass
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Denumerable
import Mathlib.Tactic

/-! Actual compact smooth cutoffs and summable weights for the common
exceptional-cone construction. The countable index includes every direction,
window size, and sampling scale, without an assumed summability certificate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace V10.ProjectionWindowWeights

theorem exists_cutoff (L : ℕ) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ z, 0 ≤ φ z) ∧ (∀ z ∈ closedBall (0 : ℂ) (L + 1), φ z = 1) := by
  obtain ⟨φ, hφ, hφc, _, hn, he⟩ := SmoothMeasureMass.exists_smooth_cutoff
    (isCompact_closedBall (0 : ℂ) (L + 1)) isOpen_univ (subset_univ _)
  exact ⟨φ, hφ, hφc, hn, he⟩

def cutoff (L : ℕ) : ℂ → ℝ := (exists_cutoff L).choose

theorem cutoff_smooth (L : ℕ) : ContDiff ℝ ∞ (cutoff L) :=
  (exists_cutoff L).choose_spec.1

theorem cutoff_compact (L : ℕ) : HasCompactSupport (cutoff L) :=
  (exists_cutoff L).choose_spec.2.1

theorem cutoff_nonneg (L : ℕ) (z : ℂ) : 0 ≤ cutoff L z :=
  (exists_cutoff L).choose_spec.2.2.1 z

theorem cutoff_eq_one (L : ℕ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) (L + 1)) :
    cutoff L z = 1 := (exists_cutoff L).choose_spec.2.2.2 z hz

def mass (L : ℕ) : ℝ := ∫ z, cutoff L z

theorem mass_pos (L : ℕ) : 0 < mass L := by
  apply (cutoff_smooth L).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (cutoff_compact L) (cutoff_nonneg L) (x := 0)
  rw [cutoff_eq_one L (mem_closedBall_self (by positivity))]
  norm_num

/-- Every compact physical window is covered by one of the actual cutoffs. -/
theorem exists_cutoff_eq_one_on {K : Set ℂ} (hK : IsCompact K) :
    ∃ L : ℕ, ∀ z ∈ K, cutoff L z = 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨L, hL⟩ := exists_nat_gt R
  refine ⟨L, fun z hz => cutoff_eq_one L ?_⟩
  exact (closedBall_subset_closedBall (show R ≤ (L : ℝ) + 1 by linarith)) (hR hz)

def cutoffWeight (L : ℕ) : ℝ := (1 / 2 : ℝ) ^ (L + 1) / (1 + mass L)

theorem cutoffWeight_pos (L : ℕ) : 0 < cutoffWeight L := by
  exact div_pos (pow_pos (by norm_num) _) (by linarith [mass_pos L])

theorem weighted_mass_le (L : ℕ) :
    cutoffWeight L * mass L ≤ (1 / 2 : ℝ) ^ (L + 1) := by
  have hd : 0 < 1 + mass L := by linarith [mass_pos L]
  unfold cutoffWeight
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hd).mpr (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (L + 1)])

theorem summable_weighted_mass : Summable (fun L => cutoffWeight L * mass L) := by
  have hg : Summable (fun L : ℕ => (1 / 2 : ℝ) ^ (L + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2)
  exact Summable.of_nonneg_of_le (fun L => (mul_pos (cutoffWeight_pos L) (mass_pos L)).le)
    weighted_mass_le hg

abbrev WindowIndex (Ω : Type*) := Ω × ℕ × ℕ

def windowWeight (Q : ℕ → ℝ) {Ω : Type*} (i : WindowIndex Ω) : ℝ :=
  cutoffWeight i.2.1 / Q i.2.2

def windowMass (Q : ℕ → ℝ) {Ω : Type*} (i : WindowIndex Ω) : ℝ :=
  windowWeight Q i * mass i.2.1

theorem windowWeight_pos {Ω : Type*} {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m)
    (i : WindowIndex Ω) : 0 < windowWeight Q i :=
  div_pos (cutoffWeight_pos _) (hQ _)

theorem windowMass_pos {Ω : Type*} {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m)
    (i : WindowIndex Ω) : 0 < windowMass Q i :=
  mul_pos (windowWeight_pos hQ i) (mass_pos _)

theorem summable_windowMass {Ω : Type*} [Fintype Ω] {Q : ℕ → ℝ}
    (hQ : ∀ m, 0 < Q m) (hQsum : Summable (fun m => (Q m)⁻¹)) :
    Summable (windowMass Q : WindowIndex Ω → ℝ) := by
  have hp := summable_weighted_mass.mul_of_nonneg hQsum
    (fun L => (mul_pos (cutoffWeight_pos L) (mass_pos L)).le)
    (fun m => (inv_pos.mpr (hQ m)).le)
  apply (summable_prod_of_nonneg (fun i : WindowIndex Ω => (windowMass_pos hQ i).le)).mpr
  refine ⟨fun dir => ?_, (hasSum_fintype _).summable⟩
  convert hp using 1
  funext i
  simp only [windowMass, windowWeight, div_eq_mul_inv]
  ring

/-- An actual bijection enumerates all directions, cutoff sizes, and scales.
No summand is discarded or repeated. -/
def enumerate (Ω : Type*) [Fintype Ω] [Nonempty Ω] : ℕ ≃ WindowIndex Ω :=
  Classical.choice (inferInstance : Nonempty (ℕ ≃ WindowIndex Ω))

theorem summable_enumerated_mass {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (hQsum : Summable (fun m => (Q m)⁻¹)) :
    Summable (fun j => windowMass Q (enumerate Ω j)) :=
  (enumerate Ω).summable_iff.mpr (summable_windowMass hQ hQsum)

theorem homogeneity_mass_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (hQsum : Summable (fun m => (Q m)⁻¹)) :
    0 < ∑' j, windowMass Q (enumerate Ω j) :=
  (summable_enumerated_mass hQ hQsum).tsum_pos
    (fun _ => (windowMass_pos hQ _).le) 0 (windowMass_pos hQ _)

#print axioms exists_cutoff_eq_one_on
#print axioms summable_enumerated_mass
#print axioms homogeneity_mass_pos
end V10.ProjectionWindowWeights
