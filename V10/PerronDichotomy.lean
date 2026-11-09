import ZeroDensity.PerronEstimates
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Differential-inequality core of Perron's two-block dichotomy

The dichotomy is proved, not assumed: the exponentially weighted difference
of unstable and stable energies is nondecreasing. Either a trajectory enters
the unstable cone and stays there, or it remains in the stable cone.
This module's scalar core must be connected to actual spectral block energies
before it is used as a theorem for an arbitrary asymptotically constant ODE.
-/

namespace V10.PerronDichotomy
open Set Filter
open scoped Topology
noncomputable section

/-- Integrating an actual differential upper inequality, without assuming
positivity of the scalar function. -/
theorem exponential_upper_of_deriv_le {p p' : ℝ → ℝ} {a b k : ℝ}
    (hab : a ≤ b) (hp : ∀ t ∈ Icc a b, HasDerivAt p (p' t) t)
    (hle : ∀ t ∈ Icc a b, p' t ≤ k * p t) :
    p b ≤ p a * Real.exp (k * (b - a)) := by
  let w : ℝ → ℝ := fun t => Real.exp (-k * (t - a)) * p t
  have hw : ∀ t ∈ Icc a b, HasDerivAt w
      (Real.exp (-k * (t - a)) * (p' t - k * p t)) t := by
    intro t ht
    have he : HasDerivAt (fun s : ℝ => Real.exp (-k * (s - a)))
        (Real.exp (-k * (t - a)) * (-k)) t := by
      simpa using (((hasDerivAt_id t).sub_const a).const_mul (-k)).exp
    have hmul := he.mul (hp t ht)
    have heq : Real.exp (-k * (t - a)) * (-k) * p t +
        Real.exp (-k * (t - a)) * p' t =
        Real.exp (-k * (t - a)) * (p' t - k * p t) := by ring
    rw [heq] at hmul
    exact hmul
  have hm : AntitoneOn w (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · exact fun t ht => (hw t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hw t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hw t (interior_subset ht)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (hle t (interior_subset ht)))
  have hh := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hh' : Real.exp (-k * (b - a)) * p b ≤ p a := by simpa [w] using hh
  calc
    p b = Real.exp (k * (b - a)) * (Real.exp (-k * (b - a)) * p b) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (k * (b - a)) * p a :=
      mul_le_mul_of_nonneg_left hh' (Real.exp_pos _).le
    _ = p a * Real.exp (k * (b - a)) := mul_comm _ _

/-- The corresponding lower comparison follows by applying the upper
comparison to the negative function. -/
theorem exponential_lower_of_le_deriv {p p' : ℝ → ℝ} {a b k : ℝ}
    (hab : a ≤ b) (hp : ∀ t ∈ Icc a b, HasDerivAt p (p' t) t)
    (hle : ∀ t ∈ Icc a b, k * p t ≤ p' t) :
    p a * Real.exp (k * (b - a)) ≤ p b := by
  have h := exponential_upper_of_deriv_le hab
    (fun t ht => (hp t ht).neg) (k := k) (fun t ht => by
      dsimp
      nlinarith [hle t ht])
  dsimp at h
  nlinarith

/-- The weighted unstable-minus-stable energy cannot change from nonnegative
to negative once the spectral-gap inequalities hold. -/
theorem unstable_cone_forward {p q p' q' : ℝ → ℝ} {T a b γ δ : ℝ}
    (hδ : 0 ≤ δ) (hTa : T ≤ a) (hab : a ≤ b)
    (hp : ∀ t ≥ T, HasDerivAt p (p' t) t)
    (hq : ∀ t ≥ T, HasDerivAt q (q' t) t)
    (hnonneg : ∀ t ≥ T, 0 ≤ p t ∧ 0 ≤ q t)
    (hpbound : ∀ t ≥ T, p' t ≤ 2 * (γ - 2 * δ) * p t + δ * (p t + q t))
    (hqbound : ∀ t ≥ T, 2 * (γ + 2 * δ) * q t - δ * (p t + q t) ≤ q' t)
    (hcone : p a ≤ q a) : p b ≤ q b := by
  have hd := exponential_lower_of_le_deriv (p := fun t => q t - p t)
    (p' := fun t => q' t - p' t) (k := 2 * γ) hab
    (fun t ht => (hq t (hTa.trans ht.1)).sub (hp t (hTa.trans ht.1)))
    (fun t ht => by
      have htT := hTa.trans ht.1
      have hn := hnonneg t htT
      have hpB := hpbound t htT
      have hqB := hqbound t htT
      have hprod := mul_nonneg hδ (add_nonneg hn.1 hn.2)
      nlinarith)
  have hleft : 0 ≤ (q a - p a) * Real.exp (2 * γ * (b - a)) :=
    mul_nonneg (sub_nonneg.mpr hcone) (Real.exp_pos _).le
  exact sub_nonneg.mp (hleft.trans hd)

/-- A true two-block energy dichotomy. Its two alternatives are derived from
actual differential inequalities; neither exponential growth alternative is
supplied as an input. -/
theorem energy_dichotomy {p q p' q' : ℝ → ℝ} {T γ δ : ℝ}
    (hδ : 0 < δ)
    (hp : ∀ t ≥ T, HasDerivAt p (p' t) t)
    (hq : ∀ t ≥ T, HasDerivAt q (q' t) t)
    (hnonneg : ∀ t ≥ T, 0 ≤ p t ∧ 0 ≤ q t)
    (hpositive : ∀ t ≥ T, 0 < p t + q t)
    (hpbound : ∀ t ≥ T, p' t ≤ 2 * (γ - 2 * δ) * p t + δ * (p t + q t))
    (hqbound : ∀ t ≥ T, 2 * (γ + 2 * δ) * q t - δ * (p t + q t) ≤ q' t) :
    (∃ C : ℝ, 0 < C ∧ ∀ t ≥ T,
      p t + q t ≤ C * Real.exp (2 * (γ - δ) * (t - T))) ∨
    (∃ T₁ ≥ T, ∃ C : ℝ, 0 < C ∧ ∀ t ≥ T₁,
      C * Real.exp (2 * (γ + δ) * (t - T₁)) ≤ p t + q t) := by
  by_cases hc : ∃ a ≥ T, p a ≤ q a
  · obtain ⟨a, haT, hacone⟩ := hc
    right
    have hcone : ∀ t ≥ a, p t ≤ q t := fun t ht =>
      unstable_cone_forward hδ.le haT ht hp hq hnonneg hpbound hqbound hacone
    have hqa : 0 < q a := by
      have hpos := hpositive a haT
      linarith
    refine ⟨a, haT, q a, hqa, ?_⟩
    intro t ht
    have hh := exponential_lower_of_le_deriv (k := 2 * (γ + δ)) ht
      (fun s hs => hq s (haT.trans hs.1)) (fun s hs => by
        have hsT := haT.trans hs.1
        have hB := hqbound s hsT
        have hconeS := hcone s hs.1
        have hprod := mul_nonneg hδ.le (sub_nonneg.mpr hconeS)
        nlinarith)
    exact hh.trans (le_add_of_nonneg_left (hnonneg t (haT.trans ht)).1)
  · left
    have hcone : ∀ t ≥ T, q t < p t := by
      intro t ht
      exact lt_of_not_ge (fun h => hc ⟨t, ht, h⟩)
    have hpT : 0 < p T := lt_of_le_of_lt (hnonneg T le_rfl).2 (hcone T le_rfl)
    refine ⟨2 * p T, by positivity, ?_⟩
    intro t ht
    have hh := exponential_upper_of_deriv_le (k := 2 * (γ - δ)) ht
      (fun s hs => hp s hs.1) (fun s hs => by
        have hB := hpbound s hs.1
        have hconeS := (hcone s hs.1).le
        have hprod := mul_nonneg hδ.le (sub_nonneg.mpr hconeS)
        nlinarith)
    have hcT := (hcone t ht).le
    nlinarith

#print axioms exponential_upper_of_deriv_le
#print axioms exponential_lower_of_le_deriv
#print axioms unstable_cone_forward
#print axioms energy_dichotomy
end
end V10.PerronDichotomy
