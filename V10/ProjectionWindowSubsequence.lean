import V10.ProjectionWindowWeights
import V10.LogHomogeneousSeries

/-! Outside the actual pole set of the enumerated potential, every fixed
direction and cutoff-size subseries is summable. The positive cutoff weight
is removed internally, giving convergence of the normalized window averages. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace V10.ProjectionWindowSubsequence
open ProjectionWindowWeights LogHomogeneousSeries

variable {Ω E : Type*} [Fintype Ω] [Nonempty Ω] [AddCommGroup E]

def windowIndexSequence (dir : Ω) (L : ℕ) (m : ℕ) : ℕ :=
  (enumerate Ω).symm (dir, L, m)

theorem windowIndexSequence_injective (dir : Ω) (L : ℕ) :
    Function.Injective (windowIndexSequence dir L) := by
  intro m k h
  have he := (enumerate Ω).symm.injective h
  exact congrArg (fun i : WindowIndex Ω => i.2.2) he

theorem summable_window_of_ne_bot {v : WindowIndex Ω → E → ℝ} {c : E}
    (hc : seriesPotential (fun j => v (enumerate Ω j)) c ≠ ⊥)
    (dir : Ω) (L : ℕ) {a : ℕ → ℝ}
    (he : ∀ m, v (dir, L, m) c = cutoffWeight L * a m) :
    Summable a := by
  have hsum : Summable (fun j => v (enumerate Ω j) c) := by
    exact (not_or.mp ((seriesPotential_eq_bot _ _).not.mp hc)).2 |> not_not.mp
  have hsub := hsum.comp_injective (windowIndexSequence_injective dir L)
  have hs : Summable (fun m => cutoffWeight L * a m) := by
    apply hsub.congr
    intro m
    change v (enumerate Ω ((enumerate Ω).symm (dir, L, m))) c = cutoffWeight L * a m
    rw [Equiv.apply_symm_apply]
    exact he m
  exact (summable_mul_left_iff (cutoffWeight_pos L).ne').mp hs

theorem window_tendsto_zero_of_ne_bot {v : WindowIndex Ω → E → ℝ} {c : E}
    (hc : seriesPotential (fun j => v (enumerate Ω j)) c ≠ ⊥)
    (dir : Ω) (L : ℕ) {a : ℕ → ℝ}
    (he : ∀ m, v (dir, L, m) c = cutoffWeight L * a m) :
    Tendsto a atTop (𝓝 0) :=
  (summable_window_of_ne_bot hc dir L he).tendsto_atTop_zero

/-- Non-pole coefficients are nonzero; the origin is genuinely a pole. -/
theorem coefficient_ne_zero {v : WindowIndex Ω → E → ℝ} {c : E}
    (hc : seriesPotential (fun j => v (enumerate Ω j)) c ≠ ⊥) : c ≠ 0 :=
  (not_or.mp ((seriesPotential_eq_bot _ _).not.mp hc)).1

#print axioms summable_window_of_ne_bot
#print axioms window_tendsto_zero_of_ne_bot
end V10.ProjectionWindowSubsequence
