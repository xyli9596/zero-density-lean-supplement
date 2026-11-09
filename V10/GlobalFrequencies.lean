import ZeroDensity.MaximalCoefficientData
import V10.ExponentialScales

/-!
# The global active frequencies of v10

The legacy project selected one maximal frequency. Here the actual finite
coefficient data determine all of Ω_a, the maximum β_*, and the nonempty
set Ω_*. No root simplicity or uniqueness of the maximizing frequency is
assumed. This supplies definitions and their algebraic properties, not
the analytic global zero-distribution theorem.
-/

noncomputable section
open Filter
open scoped Topology

namespace V10.GlobalFrequencies
open ZeroDensity.Statement ZeroDensity.CoefficientData
open ZeroDensity.MaximalCoefficientData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

def a (E : EquationData n) : ℝ := ‖omega E‖

theorem a_pos (E : EquationData n) : 0 < a E :=
  norm_pos_iff.mpr (omega_spec E).2.1

theorem weighted_norm_le (E : EquationData n) {ω : ℂ}
    (hω : ω ∈ weightedFrequencies E) : ‖ω‖ ≤ a E :=
  (omega_spec E).2.2 ω hω

def maximalFrequencies (E : EquationData n) : Finset ℂ :=
  (weightedFrequencies E).filter fun ω => ‖ω‖ = a E

theorem mem_maximalFrequencies (E : EquationData n) (ω : ℂ) :
    ω ∈ maximalFrequencies E ↔ ω ∈ weightedFrequencies E ∧ ‖ω‖ = a E := by
  simp [maximalFrequencies]

theorem maximalFrequencies_nonempty (E : EquationData n) :
    (maximalFrequencies E).Nonempty :=
  ⟨omega E, (mem_maximalFrequencies E _).mpr ⟨(omega_spec E).1, rfl⟩⟩

abbrev MaxFrequency (E : EquationData n) := {ω : ℂ // ω ∈ maximalFrequencies E}

instance (E : EquationData n) : Nonempty (MaxFrequency E) :=
  ⟨⟨omega E, (mem_maximalFrequencies E _).mpr ⟨(omega_spec E).1, rfl⟩⟩⟩

def selection (E : EquationData n) (ω : MaxFrequency E) : Selection E where
  ω := ω.val
  spec := by
    have hω := (mem_maximalFrequencies E ω.val).mp ω.property
    refine ⟨hω.1, ?_, ?_⟩
    · intro hz
      apply (a_pos E).ne'
      simpa [hz] using hω.2.symm
    · intro q hq
      rw [hω.2]
      exact weighted_norm_le E hq

def betaAt (E : EquationData n) (ω : MaxFrequency E) : ℚ :=
  ZeroDensity.MaximalCoefficientData.beta E (selection E ω)

theorem betaAt_nonneg (E : EquationData n) (ω : MaxFrequency E) : 0 ≤ betaAt E ω :=
  ZeroDensity.MaximalCoefficientData.beta_nonneg E (selection E ω)

def betaStar (E : EquationData n) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (betaAt E)

theorem betaAt_le_betaStar (E : EquationData n) (ω : MaxFrequency E) :
    betaAt E ω ≤ betaStar E :=
  Finset.le_sup' (betaAt E) (Finset.mem_univ ω)

theorem betaStar_nonneg (E : EquationData n) : 0 ≤ betaStar E := by
  let ω : MaxFrequency E := Classical.choice inferInstance
  exact (betaAt_nonneg E ω).trans (betaAt_le_betaStar E ω)

def activeFrequencies (E : EquationData n) : Finset (MaxFrequency E) :=
  Finset.univ.filter fun ω => betaAt E ω = betaStar E

theorem mem_activeFrequencies (E : EquationData n) (ω : MaxFrequency E) :
    ω ∈ activeFrequencies E ↔ betaAt E ω = betaStar E := by
  simp [activeFrequencies]

theorem activeFrequencies_nonempty (E : EquationData n) :
    (activeFrequencies E).Nonempty := by
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (betaAt E)
  exact ⟨ω, (mem_activeFrequencies E ω).mpr hω.symm⟩

theorem inactive_degree_lt (E : EquationData n) (ω : MaxFrequency E)
    (hω : ω ∉ activeFrequencies E) : betaAt E ω < betaStar E := by
  apply lt_of_le_of_ne (betaAt_le_betaStar E ω)
  exact fun he => hω ((mem_activeFrequencies E ω).mpr he)

/-- The second maximization is essential: tied exponential rates with a
    smaller polynomial degree do not contribute to the leading scale. -/
theorem inactive_scale_negligible (E : EquationData n) (ω : MaxFrequency E)
    (hω : ω ∉ activeFrequencies E) :
    Tendsto (fun r =>
      ExponentialScales.scale (a E) ((betaAt E ω : ℝ) + 1 / 2) r /
      ExponentialScales.scale (a E) ((betaStar E : ℝ) + 1 / 2) r)
      atTop (𝓝 0) := by
  apply ExponentialScales.lower_power_ratio_tendsto_zero
  have : (betaAt E ω : ℝ) < (betaStar E : ℝ) := by
    exact_mod_cast inactive_degree_lt E ω hω
  linarith

end V10.GlobalFrequencies
