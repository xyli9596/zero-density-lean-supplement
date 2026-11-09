import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Complex.Basic

namespace ZeroDensity.ExactChange
open Filter
open scoped Topology BigOperators
noncomputable section

/-- The manuscript's chain coefficients, with the negative-index term omitted
at index zero. These are computed from the actual derivative of the forward map. -/
def chainCoeff (q : ℂ → ℂ) : ℕ → ℕ → ℂ → ℂ
  | 0, 0 => fun _ => 1
  | 0, _ + 1 => fun _ => 0
  | m + 1, 0 => deriv (chainCoeff q m 0)
  | m + 1, k + 1 => fun z => deriv (chainCoeff q m (k + 1)) z + q z * chainCoeff q m k z

lemma chainCoeff_above (q : ℂ → ℂ) {m k : ℕ} (h : m < k) :
    chainCoeff q m k = fun _ => 0 := by
  induction m generalizing k with
  | zero => cases k <;> simp_all [chainCoeff]
  | succ m ih =>
    cases k with
    | zero => omega
    | succ k =>
      have h1 := ih (k := k + 1) (by omega)
      have h2 := ih (k := k) (by omega)
      simp [chainCoeff, h1, h2]

lemma chainCoeff_diagonal (q : ℂ → ℂ) (m : ℕ) (z : ℂ) :
    chainCoeff q m m z = q z ^ m := by
  induction m with
  | zero => simp [chainCoeff]
  | succ m ih =>
    rw [chainCoeff, chainCoeff_above q (by omega : m < m + 1)]
    simp [ih, pow_succ, mul_comm]

lemma chainCoeff_zero_column (q : ℂ → ℂ) (m : ℕ) :
    chainCoeff q (m + 1) 0 = fun _ => 0 := by
  induction m with
  | zero => simp [chainCoeff]
  | succ m ih =>
    change deriv (chainCoeff q (m + 1) 0) = fun _ => 0
    rw [ih]
    simp

lemma chainCoeff_analytic {q : ℂ → ℂ} {z : ℂ} (hq : AnalyticAt ℂ q z) (m k : ℕ) :
    AnalyticAt ℂ (chainCoeff q m k) z := by
  induction m generalizing k with
  | zero => cases k <;> simp [chainCoeff] <;> exact analyticAt_const
  | succ m ih =>
    cases k with
    | zero => exact (ih 0).deriv
    | succ k => exact ((ih (k + 1)).deriv).add (hq.mul (ih k))

/-- Reindexing the derivative expansion into the next row of chain coefficients. -/
lemma chain_sum_step (q : ℂ → ℂ) (m : ℕ) (z : ℂ) (w : ℕ → ℂ) :
    (∑ k ∈ Finset.range (m + 1),
      (deriv (chainCoeff q m k) z * w k +
        chainCoeff q m k z * (q z * w (k + 1)))) =
    ∑ k ∈ Finset.range (m + 2), chainCoeff q (m + 1) k z * w k := by
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun k => chainCoeff q (m + 1) k z * w k)]
  simp only [chainCoeff, add_mul, Finset.sum_add_distrib]
  have hd : deriv (chainCoeff q m (m + 1)) z = 0 := by
    rw [chainCoeff_above q (by omega : m < m + 1)]
    simp
  have hs := Finset.sum_range_succ' (fun k => deriv (chainCoeff q m k) z * w k) (m + 1)
  rw [Finset.sum_range_succ, hd, zero_mul, add_zero] at hs
  rw [hs]
  have hm : (∑ k ∈ Finset.range (m + 1), chainCoeff q m k z * (q z * w (k + 1))) =
      ∑ k ∈ Finset.range (m + 1), q z * chainCoeff q m k z * w (k + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hm]
  ring

/-- The exact chain expansion for every order, assuming only local analyticity
of the original scalar function and forward phase map. -/
theorem iteratedDeriv_comp_chain {v Φ : ℂ → ℂ} {z : ℂ}
    (hv : AnalyticAt ℂ v (Φ z)) (hΦ : AnalyticAt ℂ Φ z) (m : ℕ) :
    iteratedDeriv m (v ∘ Φ) z =
      ∑ k ∈ Finset.range (m + 1),
        chainCoeff (deriv Φ) m k z * iteratedDeriv k v (Φ z) := by
  induction m generalizing z with
  | zero => simp [chainCoeff]
  | succ m ih =>
    have heq : iteratedDeriv m (v ∘ Φ) =ᶠ[𝓝 z]
        (fun t => ∑ k ∈ Finset.range (m + 1),
          chainCoeff (deriv Φ) m k t * iteratedDeriv k v (Φ t)) := by
      filter_upwards [hΦ.eventually_analyticAt,
        hΦ.continuousAt.tendsto.eventually hv.eventually_analyticAt] with t hφt hvt
      exact ih hvt hφt
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hterm (k : ℕ) : HasDerivAt
        (fun t => chainCoeff (deriv Φ) m k t * iteratedDeriv k v (Φ t))
        (deriv (chainCoeff (deriv Φ) m k) z * iteratedDeriv k v (Φ z) +
          chainCoeff (deriv Φ) m k z *
            (deriv Φ z * iteratedDeriv (k + 1) v (Φ z))) z := by
      have hc := (chainCoeff_analytic hΦ.deriv m k).differentiableAt.hasDerivAt
      have hk : AnalyticAt ℂ (iteratedDeriv k v) (Φ z) := by
        simpa only [iteratedDeriv_eq_iterate] using hv.iterated_deriv k
      have hd := hk.differentiableAt.hasDerivAt
      have hcomp := hd.comp z hΦ.differentiableAt.hasDerivAt
      have hm := hc.mul hcomp
      convert hm using 1 <;> first
      | rfl
      | (simp only [Function.comp_def, Pi.mul_def, ← iteratedDeriv_succ]; ring)
    rw [(HasDerivAt.fun_sum (fun k _ => hterm k)).deriv]
    exact chain_sum_step (deriv Φ) m z (fun k => iteratedDeriv k v (Φ z))

lemma chain_sum_padded (q : ℂ → ℂ) {m n : ℕ} (hmn : m ≤ n) (z : ℂ) (w : ℕ → ℂ) :
    (∑ k ∈ Finset.range (m + 1), chainCoeff q m k z * w k) =
      ∑ k ∈ Finset.range (n + 1), chainCoeff q m k z * w k := by
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkm
  have hmk : m < k := by simp only [Finset.mem_range] at hkm; omega
  simp [chainCoeff_above q hmk]

/-- Exact phase coefficients evaluated at the original coordinate. Evaluating this
at an inverse branch gives the coefficients in the phase equation. -/
def phaseCoeff (n : ℕ) (B : ℕ → ℂ → ℂ) (Φ : ℂ → ℂ) (k : ℕ) (t : ℂ) : ℂ :=
  (chainCoeff (deriv Φ) n k t +
    ∑ j ∈ Finset.range n, B j t * chainCoeff (deriv Φ) j k t) / (deriv Φ t) ^ n

lemma normalized_sum_identity (q : ℂ → ℂ) (n : ℕ) (B : ℕ → ℂ)
    (z : ℂ) (w : ℕ → ℂ) :
    (∑ k ∈ Finset.range (n + 1), chainCoeff q n k z * w k) +
      (∑ j ∈ Finset.range n, B j *
        ∑ k ∈ Finset.range (j + 1), chainCoeff q j k z * w k) =
    q z ^ n * w n + ∑ k ∈ Finset.range n,
      (chainCoeff q n k z + ∑ j ∈ Finset.range n, B j * chainCoeff q j k z) * w k := by
  have hp : (∑ j ∈ Finset.range n, B j *
      ∑ k ∈ Finset.range (j + 1), chainCoeff q j k z * w k) =
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range (n + 1),
        B j * chainCoeff q j k z * w k := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [chain_sum_padded q (by simp only [Finset.mem_range] at hj; omega : j ≤ n),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hp, Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_mul]
  rw [Finset.sum_range_succ, chainCoeff_diagonal]
  have hz : (∑ j ∈ Finset.range n, B j * chainCoeff q j n z) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [chainCoeff_above q (Finset.mem_range.mp hj)]
  rw [hz]
  ring

/-- Substitution into an actual normalized scalar equation and division by the
nonzero phase derivative yields the exact transformed scalar equation. The
coefficient of order `n-1` may be zero (the manuscript's reduced equation). -/
theorem normalized_equation_change {n : ℕ} {B : ℕ → ℂ → ℂ} {v Φ : ℂ → ℂ} {t : ℂ}
    (hv : AnalyticAt ℂ v (Φ t)) (hΦ : AnalyticAt ℂ Φ t) (hq : deriv Φ t ≠ 0)
    (heq : iteratedDeriv n (v ∘ Φ) t + ∑ j ∈ Finset.range n,
      B j t * iteratedDeriv j (v ∘ Φ) t = 0) :
    iteratedDeriv n v (Φ t) + ∑ k ∈ Finset.range n,
      phaseCoeff n B Φ k t * iteratedDeriv k v (Φ t) = 0 := by
  simp_rw [iteratedDeriv_comp_chain hv hΦ] at heq
  rw [normalized_sum_identity] at heq
  have hd : (deriv Φ t) ^ n ≠ 0 := pow_ne_zero n hq
  apply (mul_eq_zero.mp (show (deriv Φ t) ^ n *
      (iteratedDeriv n v (Φ t) + ∑ k ∈ Finset.range n,
        phaseCoeff n B Φ k t * iteratedDeriv k v (Φ t)) = 0 from ?_)).resolve_left hd
  rw [mul_add, Finset.mul_sum]
  convert heq using 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  unfold phaseCoeff
  field_simp

/-- In the reduced equation the numerator has exactly the manuscript's range
`0 ≤ j ≤ n-2`, written `range (n-1)` to include order two without exceptions. -/
theorem phaseCoeff_reduced {n : ℕ} (hn : 1 ≤ n) {B : ℕ → ℂ → ℂ} {Φ : ℂ → ℂ}
    {k : ℕ} {t : ℂ} (hB : B (n - 1) t = 0) :
    phaseCoeff n B Φ k t =
      (chainCoeff (deriv Φ) n k t + ∑ j ∈ Finset.range (n - 1),
        B j t * chainCoeff (deriv Φ) j k t) / (deriv Φ t) ^ n := by
  have hsum : (∑ j ∈ Finset.range n, B j t * chainCoeff (deriv Φ) j k t) =
      ∑ j ∈ Finset.range (n - 1), B j t * chainCoeff (deriv Φ) j k t := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [Finset.sum_range_succ, hB]
    simp
  unfold phaseCoeff
  rw [hsum]

/-- Evaluating the exact transformed coefficients at a fixed inverse branch gives
an equation at the phase coordinate itself. -/
theorem phase_equation_at_inverse {n : ℕ} {B : ℕ → ℂ → ℂ} {v Φ ψ : ℂ → ℂ} {s : ℂ}
    (hinv : Φ (ψ s) = s) (hv : AnalyticAt ℂ v s)
    (hΦ : AnalyticAt ℂ Φ (ψ s)) (hq : deriv Φ (ψ s) ≠ 0)
    (heq : iteratedDeriv n (v ∘ Φ) (ψ s) + ∑ j ∈ Finset.range n,
      B j (ψ s) * iteratedDeriv j (v ∘ Φ) (ψ s) = 0) :
    iteratedDeriv n v s + ∑ k ∈ Finset.range n,
      phaseCoeff n B Φ k (ψ s) * iteratedDeriv k v s = 0 := by
  have hv' : AnalyticAt ℂ v (Φ (ψ s)) := hinv.symm ▸ hv
  simpa only [hinv] using normalized_equation_change hv' hΦ hq heq

end
end ZeroDensity.ExactChange
