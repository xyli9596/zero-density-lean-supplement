import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-!
# Algebra and topology of the exceptional cone in v10 Proposition 1.5

The potential takes values in EReal, so its value at a pole really is
minus infinity. Logarithmic homogeneity implies invariance of that locus,
forces the origin into it (if the potential has no +infinity there), and
can be normalized without changing the exceptional set. A separate
measure-zero hypothesis gives density of its complement. Construction
of the plurisubharmonic potential and the polar/projective assertions
remain unproved analytic steps, not axioms of this module.
-/

noncomputable section
open MeasureTheory Set

namespace V10.ExceptionalCone
variable {E : Type*} [AddCommMonoid E] [Module ℂ E]

def LogHomogeneous (Ψ : E → EReal) (S : ℝ) : Prop :=
  ∀ κ : ℂ, κ ≠ 0 → ∀ c : E,
    Ψ (κ • c) = Ψ c + ((S * Real.log ‖κ‖ : ℝ) : EReal)

def exceptionalSet (Ψ : E → EReal) : Set E := {c | Ψ c = ⊥}

theorem smul_mem_iff {Ψ : E → EReal} {S : ℝ}
    (hΨ : LogHomogeneous Ψ S) {κ : ℂ} (hκ : κ ≠ 0) (c : E) :
    κ • c ∈ exceptionalSet Ψ ↔ c ∈ exceptionalSet Ψ := by
  change Ψ (κ • c) = ⊥ ↔ Ψ c = ⊥
  rw [hΨ κ hκ c, EReal.add_eq_bot_iff]
  exact or_iff_left (EReal.coe_ne_bot _)

theorem zero_mem {Ψ : E → EReal} {S : ℝ}
    (hΨ : LogHomogeneous Ψ S) (hS : S ≠ 0) (htop : Ψ 0 ≠ ⊤) :
    (0 : E) ∈ exceptionalSet Ψ := by
  have he := hΨ (Real.exp 1 : ℂ) (by exact_mod_cast Real.exp_ne_zero 1) 0
  have hnorm : ‖(Real.exp 1 : ℂ)‖ = Real.exp 1 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1)]
  have hlog : Real.log ‖(Real.exp 1 : ℂ)‖ = 1 := by rw [hnorm, Real.log_exp]
  have hs : Ψ 0 = Ψ 0 + (S : EReal) := by
    simpa only [smul_zero, hlog, mul_one] using he
  change Ψ 0 = ⊥
  by_contra hbot
  have ht := congrArg EReal.toReal hs
  rw [EReal.toReal_add htop hbot (EReal.coe_ne_top S) (EReal.coe_ne_bot S),
    EReal.toReal_coe] at ht
  exact hS (by linarith)

theorem closed_under_all_scalars {Ψ : E → EReal} {S : ℝ}
    (hΨ : LogHomogeneous Ψ S) (hS : S ≠ 0) (htop : Ψ 0 ≠ ⊤)
    {c : E} (hc : c ∈ exceptionalSet Ψ) (κ : ℂ) :
    κ • c ∈ exceptionalSet Ψ := by
  by_cases hκ : κ = 0
  · simpa [hκ] using zero_mem hΨ hS htop
  · exact (smul_mem_iff hΨ hκ c).mpr hc

def normalizedPotential (Ψ : E → EReal) (S : ℝ) (c : E) : EReal :=
  ((S⁻¹ : ℝ) : EReal) * Ψ c

theorem normalized_logHomogeneous {Ψ : E → EReal} {S : ℝ}
    (hΨ : LogHomogeneous Ψ S) (hS : 0 < S) :
    LogHomogeneous (normalizedPotential Ψ S) 1 := by
  intro κ hκ c
  unfold normalizedPotential
  rw [hΨ κ hκ c,
    EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast (inv_pos.mpr hS).le)
      (EReal.coe_ne_top _), ← EReal.coe_mul]
  congr 1
  congr 1
  simp [hS.ne']

omit [AddCommMonoid E] [Module ℂ E] in
theorem normalized_exceptionalSet {Ψ : E → EReal} {S : ℝ} (hS : 0 < S) :
    exceptionalSet (normalizedPotential Ψ S) = exceptionalSet Ψ := by
  ext c
  change ((S⁻¹ : ℝ) : EReal) * Ψ c = ⊥ ↔ Ψ c = ⊥
  by_cases hb : Ψ c = ⊥
  · simp [hb, EReal.coe_mul_bot_of_pos (inv_pos.mpr hS)]
  · by_cases ht : Ψ c = ⊤
    · simp [ht, EReal.coe_mul_top_of_pos (inv_pos.mpr hS)]
    · have hm : ((S⁻¹ : ℝ) : EReal) * Ψ c =
          ((S⁻¹ * (Ψ c).toReal : ℝ) : EReal) := by
        rw [EReal.coe_mul, EReal.coe_toReal ht hb]
      rw [hm]
      exact iff_of_false (EReal.coe_ne_bot _) hb

theorem dense_complement_of_null
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] {A : Set X} (hA : μ A = 0) :
    Dense Aᶜ := by
  exact μ.dense_of_ae (show ∀ᵐ x ∂μ, x ∈ Aᶜ from by simpa only [ae_iff, mem_compl_iff,
    not_not, ofPred_mem_eq] using hA)

end V10.ExceptionalCone
