import ZeroDensity.Corollary
import ZeroDensity.ConvergenceExponent
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Explicit input data and target of manuscript Theorem 1.1.

`Theorem11Target` is a proposition, not a proved theorem. The missing analytic
implication is intentionally not declared as an axiom or put into `AdmissiblePair`.
The zero-counting target uses the actual divisor counts from CountGeometry.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators

namespace ZeroDensity.Statement
open CountGeometry Corollary FiniteJumps

attribute [local instance] Classical.propDecidable

structure EquationData (n : ℕ) where
  order_ge_two : 2 ≤ n
  frequencies : Fin n → Finset ℂ
  multipliers : (j : Fin n) → ℂ → Polynomial ℂ
  multiplier_nonzero : ∀ j μ, μ ∈ frequencies j → multipliers j μ ≠ 0
  reduced : ∀ j : Fin n, j.val = n - 1 → frequencies j = ∅
  nonzero_frequency : ∃ j : Fin n, ∃ μ ∈ frequencies j, μ ≠ 0

def EquationData.coefficient {n : ℕ} (E : EquationData n) (j : Fin n) (z : ℂ) : ℂ :=
  ∑ μ ∈ E.frequencies j, (E.multipliers j μ).eval z * Complex.exp (μ * z)

def IsSolution {n : ℕ} (E : EquationData n) (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ z : ℂ,
    iteratedDeriv n f z + ∑ j : Fin n, E.coefficient j z * iteratedDeriv j.val f z = 0

def SolvesPhaseEquation (n : ℕ) (b : Fin n → ℂ → ℂ) (v : ℂ → ℂ)
    (S : Set ℂ) : Prop :=
  ∀ s ∈ S, iteratedDeriv n v s + ∑ j : Fin n, b j s * iteratedDeriv j.val v s = 0

/-- The two admissibility conditions from the manuscript, with explicit maps
and the original coefficient-limit hypotheses. No indicator or count is assumed. -/
structure AdmissiblePair {n : ℕ} (E : EquationData n) where
  left : ℝ
  right : ℝ
  S₀ : ℝ
  a : ℝ
  β : ℝ
  left_lt_right : left < right
  opening_lt_pi : right - left < Real.pi
  radius_pos : 0 < S₀
  a_pos : 0 < a
  beta_nonneg : 0 ≤ β
  beta_rational : ∃ q : ℚ, β = q
  domain : Set ℂ
  domain_open : IsOpen domain
  domain_preconnected : IsPreconnected domain
  forward : ℂ → ℂ
  inverse : ℂ → ℂ
  forward_maps : MapsTo forward domain (angularSector S₀ left right)
  inverse_maps : MapsTo inverse (angularSector S₀ left right) domain
  inverse_left : ∀ z ∈ domain, inverse (forward z) = z
  inverse_right : ∀ s ∈ angularSector S₀ left right, forward (inverse s) = s
  forward_analytic : AnalyticOnNhd ℂ forward domain
  inverse_boundary_analytic : AnalyticOnNhd ℂ inverse (closure (angularSector S₀ left right))
  inverse_radius : ∀ α₁ α₂ : ℝ, left < α₁ → α₁ ≤ α₂ → α₂ < right →
    TendstoUniformlyOn
      (fun (R θ : ℝ) => ‖inverse ((R : ℂ) * Complex.exp (θ * Complex.I))‖ -
        (Real.log R - β * Real.log (Real.log R)) / a)
      (fun _ => 0) atTop (Icc α₁ α₂)
  phase_coefficients : Fin n → ℂ → ℂ
  phase_limits : Fin n → ℂ
  phase_analytic : ∀ j, AnalyticOnNhd ℂ (phase_coefficients j)
    (angularSector S₀ left right)
  phase_limit : ∀ j α₁ α₂, left < α₁ → α₁ ≤ α₂ → α₂ < right →
    TendstoUniformlyOn
      (fun (R θ : ℝ) => phase_coefficients j ((R : ℂ) * Complex.exp (θ * Complex.I)))
      (fun _ => phase_limits j) atTop (Icc α₁ α₂)
  transforms : ∀ f : ℂ → ℂ, IsSolution E f →
    SolvesPhaseEquation n phase_coefficients (f ∘ inverse) (angularSector S₀ left right)

def IsFiniteStepDensity (left right : ℝ) (M : ℝ → ℝ) : Prop :=
  ∃ s : Finset ℝ, ∃ w : ℝ → ℝ,
    (∀ η ∈ s, η ∈ Ioo left right ∧ 0 < w η) ∧ M = density s w

/-- Formal target for Theorem 1.1, including its infinite-zero-exponent consequence.
This proposition has no proof yet. -/
def Theorem11Target : Prop :=
  ∀ (n : ℕ) (E : EquationData n) (P : AdmissiblePair E),
    ∃ family : Finset (ℝ → ℝ),
      (∀ M ∈ family, IsFiniteStepDensity P.left P.right M) ∧
      ∀ f : ℂ → ℂ, IsSolution E f → f ≠ 0 →
        ∃ M ∈ family, CountingLaw f P.inverse P.S₀ P.left P.right P.a P.β M ∧
          ((∃ θ ∈ Ioo P.left P.right, M θ ≠ 0) →
            ConvergenceExponent.InfiniteZeroExponent f)

theorem finite_step_monotone {l u : ℝ} {M : ℝ → ℝ}
    (hM : IsFiniteStepDensity l u M) : Monotone M := by
  rcases hM with ⟨s, w, hin, rfl⟩
  exact density_monotone s w (fun η hη => (hin η hη).2.le)

theorem finite_step_right_continuous {l u : ℝ} {M : ℝ → ℝ}
    (hM : IsFiniteStepDensity l u M) (θ : ℝ) :
    ContinuousWithinAt M (Ici θ) θ := by
  rcases hM with ⟨s, w, _hin, rfl⟩
  exact density_continuousWithinAt_right s w θ

theorem finite_step_zero_near_left {l u : ℝ} {M : ℝ → ℝ}
    (hM : IsFiniteStepDensity l u M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ ∈ Ioo l (l + δ), M θ = 0 := by
  rcases hM with ⟨s, w, hin, rfl⟩
  have hno : ∀ η ∈ s, η ∉ Icc l l := by
    intro η hη he
    exact (not_le_of_gt (hin η hη).1.1) he.2
  obtain ⟨δ, hδ, hd⟩ := finite_buffer s le_rfl hno
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ
  unfold density
  apply Finset.sum_eq_zero
  intro η hη
  have hlo := (hin η hη).1.1
  have hhi : l + δ < η := by
    have hnot := hd η hη
    have : ¬ η ≤ l + δ := fun hb => hnot ⟨by linarith, hb⟩
    exact lt_of_not_ge this
  simp [not_le_of_gt (hθ.2.trans hhi)]

/-- Corollary 1.2 in the manuscript's abstract notation. The counting law is
the explicit premise supplied by Theorem 1.1; no extra growth assumption occurs. -/
theorem corollary_1_2_from_counting_law {n : ℕ} {E : EquationData n}
    (P : AdmissiblePair E) {f : ℂ → ℂ} (hf : IsSolution E f) (hne : f ≠ 0)
    {M : ℝ → ℝ} (hM : IsFiniteStepDensity P.left P.right M)
    (hlaw : CountingLaw f P.inverse P.S₀ P.left P.right P.a P.β M)
    {α₁ α₂ : ℝ} (hleft : P.left < α₁) (horder : α₁ < α₂) (hright : α₂ < P.right)
    (hfree : ∀ θ ∈ Icc α₁ α₂, ContinuousAt M θ) :
    (fun r => count f (closedPullback P.inverse P.S₀ α₁ α₂) r) =o[atTop] scale P.a P.β := by
  rcases hM with ⟨s, w, _hin, rfl⟩
  exact Corollary.corollary_1_2 hf.1 hne s w hlaw hleft horder hright hfree

/-- The final infinite-exponent assertion of Theorem 1.1 follows from its
counting law and its finite positive step-density description. -/
theorem infinite_exponent_from_counting_law {n : ℕ} {E : EquationData n}
    (P : AdmissiblePair E) {f : ℂ → ℂ} (hf : IsSolution E f)
    {M : ℝ → ℝ} (hM : IsFiniteStepDensity P.left P.right M)
    (hlaw : CountingLaw f P.inverse P.S₀ P.left P.right P.a P.β M)
    (hpositive : ∃ θ ∈ Ioo P.left P.right, M θ ≠ 0) :
    ConvergenceExponent.InfiniteZeroExponent f := by
  rcases hM with ⟨s, w, hin, rfl⟩
  have hs : s.Nonempty := by
    by_contra hn
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rcases hpositive with ⟨θ, _hθ, hθM⟩
    simpa [he, density] using hθM
  obtain ⟨α₁, α₂, hl, ho, hr, hc₁, hc₂, hp⟩ :=
    exists_positive_interval s w hs (fun η hη => (hin η hη).1)
      (fun η hη => (hin η hη).2)
  have hc := hlaw α₁ α₂ hl ho hr hc₁ hc₂
  exact ConvergenceExponent.infiniteExponent_of_positive_exp_count hf.1
    (pullback P.inverse P.S₀ α₁ α₂) P.a_pos hp (by simpa only [scale] using hc)

#print axioms finite_step_monotone
#print axioms finite_step_right_continuous
#print axioms finite_step_zero_near_left
#print axioms corollary_1_2_from_counting_law
#print axioms infinite_exponent_from_counting_law

end ZeroDensity.Statement
