import V10.LogHomogeneousSeries
import V10.PluriPotentialSeries
import Mathlib.Tactic

/-!
# Local plurisuperharmonic representation of the constructed series potential

This connects the genuine extended series potential with a sum of genuine
nonnegative plurisuperharmonic deficits. In particular, neither convergence
at every point nor finite potential values at the exceptional set are assumed.
The separate holomorphic-average modules must supply the summand data.
-/

noncomputable section
open Set Metric
open scoped Topology ENNReal
namespace V10.LogHomogeneousPluriSeries
open LogHomogeneousSeries PluriPotentialSeries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def puncturedDeficit (v : ℕ → E → ℝ) (b : ℕ → ℝ) (j : ℕ) (c : E) : ℝ≥0∞ := by
  classical
  exact if c = 0 then ∞ else ENNReal.ofReal (b j - v j c)

omit [NormedSpace ℂ E] in
theorem deficit_tsum_at_zero (v : ℕ → E → ℝ) (b : ℕ → ℝ) :
    (∑' j, puncturedDeficit v b j 0) = ∞ := by
  simp [puncturedDeficit]

/-- On any coefficient domain with a summable common upper bound, the
constructed potential is a finite constant minus a genuinely extended
plurisuperharmonic sum. The equality includes the origin and every divergent
point; there is no exceptional-set omission. -/
theorem local_pluri_representation {v : ℕ → E → ℝ} {b : ℕ → ℝ} {U : Set E}
    (hb : Summable b) (hbound : ∀ c ∈ U, c ≠ 0 → ∀ j, v j c ≤ b j)
    (hpluri : ∀ j, PlurisuperharmonicOn (puncturedDeficit v b j) U) :
    ∃ D : E → ℝ≥0∞, PlurisuperharmonicOn D U ∧
      ∀ c ∈ U, seriesPotential v c = ((∑' j, b j : ℝ) : EReal) - (D c : EReal) := by
  refine ⟨fun c => ∑' j, puncturedDeficit v b j c, PlurisuperharmonicOn.tsum hpluri, ?_⟩
  intro c hc
  by_cases hz : c = 0
  · subst c
    dsimp only
    rw [deficit_tsum_at_zero]
    simp [seriesPotential]
  · simpa only [puncturedDeficit, if_neg hz] using
      seriesPotential_eq_upper_sub hb hz (hbound c hc hz)

/-- All algebraic parts of the exceptional cone construction, together with
the local genuine supermean representation, from the individual summands.
Analyticity, Gaussian bounds, and the actual averaged-summand identities are
not replaced by assumptions on the final potential. -/
theorem constructed_potential {v : ℕ → E → ℝ} {a : ℕ → ℝ}
    (ha : Summable a)
    (hscale : ∀ κ : ℂ, κ ≠ 0 → ∀ c : E, c ≠ 0 → ∀ j,
      v j (κ • c) = v j c + a j * Real.log ‖κ‖)
    (hgood : ∃ c : E, c ≠ 0 ∧ Summable (fun j => v j c))
    (hlocal : ∀ B : ℝ, 1 < B → ∃ b : ℕ → ℝ, Summable b ∧
      (∀ c ∈ ball (0 : E) B, c ≠ 0 → ∀ j, v j c ≤ b j) ∧
      (∀ j, PlurisuperharmonicOn (puncturedDeficit v b j) (ball (0 : E) B))) :
    ExceptionalCone.LogHomogeneous (seriesPotential v) (∑' j, a j) ∧
    (∃ c : E, seriesPotential v c ≠ ⊥) ∧
    (∀ c : E, ∀ κ : ℂ, seriesPotential v c = ⊥ → seriesPotential v (κ • c) = ⊥) ∧
    (∀ B : ℝ, 1 < B → ∃ (C : ℝ) (D : E → ℝ≥0∞),
      PlurisuperharmonicOn D (ball (0 : E) B) ∧
      ∀ c ∈ ball (0 : E) B, seriesPotential v c = (C : EReal) - (D c : EReal)) := by
  obtain ⟨c, hc, hs⟩ := hgood
  refine ⟨seriesPotential_logHomogeneous ha hscale,
    seriesPotential_not_identically_bot hc hs,
    fun c κ hp => seriesPotential_pole_cone ha hscale hp κ, ?_⟩
  intro B hB
  obtain ⟨b, hb, hbound, hp⟩ := hlocal B hB
  obtain ⟨D, hD, he⟩ := local_pluri_representation hb hbound hp
  exact ⟨∑' j, b j, D, hD, he⟩

#print axioms constructed_potential
end V10.LogHomogeneousPluriSeries
