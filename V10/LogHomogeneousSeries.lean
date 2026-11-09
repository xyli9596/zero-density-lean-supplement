import V10.ExceptionalCone
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# Constructing the logarithmically homogeneous series potential

This constructs the extended-real potential from its actual real summands on
the punctured coefficient space. Nonsummable series and the origin are poles.
Logarithmic homogeneity is proved from the individual scaling identities and
the summable coefficient sequence, including divergent points. The analytic
PSH property remains a separate obligation, via local upper bounds/deficits.
-/

noncomputable section
open Set
open scoped Topology ENNReal
namespace V10.LogHomogeneousSeries

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def seriesPotential (v : ℕ → E → ℝ) (c : E) : EReal := by
  classical
  exact if c = 0 then ⊥ else if Summable (fun j => v j c) then ((∑' j, v j c : ℝ) : EReal) else ⊥

omit [Module ℂ E] in
theorem seriesPotential_eq_bot (v : ℕ → E → ℝ) (c : E) :
    seriesPotential v c = ⊥ ↔ c = 0 ∨ ¬Summable (fun j => v j c) := by
  unfold seriesPotential
  split_ifs <;> simp_all

omit [Module ℂ E] in
theorem seriesPotential_ne_top (v : ℕ → E → ℝ) (c : E) :
    seriesPotential v c ≠ ⊤ := by
  unfold seriesPotential
  split_ifs <;> simp

theorem summable_at_smul_iff {v : ℕ → E → ℝ} {a : ℕ → ℝ}
    (ha : Summable a)
    (hscale : ∀ κ : ℂ, κ ≠ 0 → ∀ c : E, c ≠ 0 → ∀ j,
      v j (κ • c) = v j c + a j * Real.log ‖κ‖)
    {κ : ℂ} (hκ : κ ≠ 0) {c : E} (hc : c ≠ 0) :
    Summable (fun j => v j (κ • c)) ↔ Summable (fun j => v j c) := by
  have he : (fun j => v j (κ • c)) = fun j => v j c + a j * Real.log ‖κ‖ :=
    funext (hscale κ hκ c hc)
  rw [he]
  have hb := ha.mul_right (Real.log ‖κ‖)
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using h.sub hb
  · exact fun h => h.add hb

/-- The actual series defines a logarithmically homogeneous potential, even
at all points where the series diverges. -/
theorem seriesPotential_logHomogeneous {v : ℕ → E → ℝ} {a : ℕ → ℝ}
    (ha : Summable a)
    (hscale : ∀ κ : ℂ, κ ≠ 0 → ∀ c : E, c ≠ 0 → ∀ j,
      v j (κ • c) = v j c + a j * Real.log ‖κ‖) :
    ExceptionalCone.LogHomogeneous (seriesPotential v) (∑' j, a j) := by
  intro κ hκ c
  by_cases hc : c = 0
  · subst c
    simp [seriesPotential]
  · have hlc : κ • c ≠ 0 := smul_ne_zero hκ hc
    have hs := summable_at_smul_iff ha hscale hκ hc
    by_cases hv : Summable (fun j => v j c)
    · simp only [seriesPotential, if_neg hc, if_neg hlc, if_pos hv, if_pos (hs.mpr hv)]
      rw [← EReal.coe_add]
      congr 1
      simp_rw [hscale κ hκ c hc]
      rw [hv.tsum_add (ha.mul_right _), tsum_mul_right]
    · simp [seriesPotential, hc, hlc, hv, mt hs.mp hv]

theorem seriesPotential_pole_cone {v : ℕ → E → ℝ} {a : ℕ → ℝ}
    (ha : Summable a)
    (hscale : ∀ κ : ℂ, κ ≠ 0 → ∀ c : E, c ≠ 0 → ∀ j,
      v j (κ • c) = v j c + a j * Real.log ‖κ‖)
    {c : E} (hc : seriesPotential v c = ⊥) (κ : ℂ) :
    seriesPotential v (κ • c) = ⊥ := by
  by_cases hκ : κ = 0
  · simp [hκ, seriesPotential]
  · have h := seriesPotential_logHomogeneous ha hscale κ hκ c
    rw [hc] at h
    simpa using h

omit [Module ℂ E] in
/-- The constructed potential is genuinely nontrivial as soon as there is
one nonzero absolute-convergence point. -/
theorem seriesPotential_not_identically_bot {v : ℕ → E → ℝ}
    {c : E} (hc : c ≠ 0) (hv : Summable (fun j => v j c)) :
    ∃ c : E, seriesPotential v c ≠ ⊥ := by
  refine ⟨c, ?_⟩
  simp [seriesPotential, hc, hv]

/-- Summability is equivalent to finiteness of the genuine nonnegative
deficit series whenever the upper bounds are summable. -/
theorem summable_iff_deficit_finite {v b : ℕ → ℝ} (hb : Summable b)
    (hbound : ∀ j, v j ≤ b j) :
    Summable v ↔ (∑' j, ENNReal.ofReal (b j - v j)) ≠ ∞ := by
  constructor
  · exact fun hv => (hb.sub hv).tsum_ofReal_ne_top
  · intro h
    have hd := ENNReal.summable_toReal h
    simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr (hbound _))] at hd
    simpa only [sub_sub_cancel] using hb.sub hd

omit [Module ℂ E] in
/-- Local upper-bound representation of the constructed series potential.
At divergent points the right hand side really is minus infinity. This is
the algebraic bridge to the proved extended plurisuperharmonic series. -/
theorem seriesPotential_eq_upper_sub {v : ℕ → E → ℝ} {b : ℕ → ℝ}
    (hb : Summable b) {c : E} (hc : c ≠ 0) (hbound : ∀ j, v j c ≤ b j) :
    seriesPotential v c = ((∑' j, b j : ℝ) : EReal) -
      ((∑' j, ENNReal.ofReal (b j - v j c) : ℝ≥0∞) : EReal) := by
  have hdnonneg : ∀ j, 0 ≤ b j - v j c := fun j => sub_nonneg.mpr (hbound j)
  by_cases hv : Summable (fun j => v j c)
  · have hd := hb.sub hv
    rw [← ENNReal.ofReal_tsum_of_nonneg hdnonneg hd]
    have hsnonneg : 0 ≤ ∑' j, (b j - v j c) := tsum_nonneg hdnonneg
    rw [EReal.coe_ennreal_ofReal, max_eq_left hsnonneg]
    simp only [seriesPotential, if_neg hc, if_pos hv]
    rw [← EReal.coe_sub, hb.tsum_sub hv, sub_sub_cancel]
  · have hi : (∑' j, ENNReal.ofReal (b j - v j c)) = ∞ :=
      not_ne_iff.mp (mt (summable_iff_deficit_finite hb hbound).mpr hv)
    simp [seriesPotential, hc, hv, hi]

#print axioms seriesPotential_logHomogeneous
#print axioms seriesPotential_pole_cone
end V10.LogHomogeneousSeries
