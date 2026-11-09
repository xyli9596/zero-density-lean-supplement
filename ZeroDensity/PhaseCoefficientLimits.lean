import ZeroDensity.ExactChange
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
Conditional analytic assembly of the phase-coefficient limit. The hypotheses are
intermediate estimates on the actual original coefficients and the actual chain
coefficients from `ExactChange`, not the desired phase-coefficient limit.
Deriving these estimates from admissibility and bounds on derivatives of the
phase map remains a separate obligation.
-/
namespace ZeroDensity.PhaseCoefficientLimits
open Filter Asymptotics
open scoped Topology
noncomputable section

/-- A chain coefficient of size `O(q^k)` divided by a strictly higher power of a
phase derivative escaping to infinity tends to zero. -/
lemma chain_quotient_zero {α : Type*} {l : Filter α} {t : α → ℂ} {Φ : ℂ → ℂ}
    {m k j : ℕ} (hkj : k < j)
    (hq : Tendsto (fun x => ‖deriv Φ (t x)‖) l atTop)
    (hC : (fun x => ExactChange.chainCoeff (deriv Φ) m k (t x)) =O[l]
      (fun x => deriv Φ (t x) ^ k)) :
    Tendsto (fun x => ExactChange.chainCoeff (deriv Φ) m k (t x) /
      deriv Φ (t x) ^ j) l (𝓝 0) := by
  have ht : Tendsto (fun x => deriv Φ (t x)) l (Bornology.cobounded ℂ) :=
    tendsto_norm_atTop_iff_cobounded.mp hq
  have hp := (isLittleO_pow_pow_cobounded_of_lt (R := ℂ) hkj).comp_tendsto ht
  exact (hC.trans_isLittleO hp).tendsto_div_nhds_zero

lemma normalized_chain_term_limit {α : Type*} {l : Filter α} {t : α → ℂ}
    {Φ : ℂ → ℂ} {B : ℕ → ℂ → ℂ} {c : ℕ → ℂ} {n k j : ℕ} (hj : j < n)
    (hq : Tendsto (fun x => ‖deriv Φ (t x)‖) l atTop)
    (hB : Tendsto (fun x => B j (t x) / deriv Φ (t x) ^ (n - j)) l (𝓝 (c j)))
    (hC : (fun x => ExactChange.chainCoeff (deriv Φ) j k (t x)) =O[l]
      (fun x => deriv Φ (t x) ^ k)) :
    Tendsto (fun x => B j (t x) * ExactChange.chainCoeff (deriv Φ) j k (t x) /
      deriv Φ (t x) ^ n) l (𝓝 (if j = k then c k else 0)) := by
  have hnz : ∀ᶠ x in l, deriv Φ (t x) ≠ 0 := by
    filter_upwards [hq.eventually_gt_atTop 0] with x hx
    exact norm_pos_iff.mp hx
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · have hz : (fun x => B j (t x) * ExactChange.chainCoeff (deriv Φ) j k (t x) /
        deriv Φ (t x) ^ n) = fun _ => 0 := by
      funext x
      simp [ExactChange.chainCoeff_above (deriv Φ) hjk]
    simp only [hz, if_neg (Nat.ne_of_lt hjk)]
    exact tendsto_const_nhds
  · have ht := hB
    simp only [ite_true]
    refine ht.congr' ?_
    filter_upwards [hnz] with x hx
    rw [ExactChange.chainCoeff_diagonal]
    have hp : deriv Φ (t x) ^ n =
        deriv Φ (t x) ^ (n - j) * deriv Φ (t x) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj.le]
    rw [hp]
    field_simp
  · have ht := hB.mul (chain_quotient_zero hkj hq hC)
    have ht' : Tendsto (fun x => (B j (t x) / deriv Φ (t x) ^ (n - j)) *
        (ExactChange.chainCoeff (deriv Φ) j k (t x) / deriv Φ (t x) ^ j)) l (𝓝 0) := by
      simpa using ht
    simp only [if_neg (Nat.ne_of_gt hkj)]
    refine ht'.congr' ?_
    filter_upwards [hnz] with x hx
    have hp : deriv Φ (t x) ^ n =
        deriv Φ (t x) ^ (n - j) * deriv Φ (t x) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj.le]
    rw [hp]
    field_simp

/-- The exact phase coefficients converge to the original normalized coefficient
limits. The highest subleading limit may be zero; no nonzero-density condition
or spectral assertion is used. -/
theorem phaseCoeff_limit {α : Type*} {l : Filter α} {t : α → ℂ}
    {Φ : ℂ → ℂ} {B : ℕ → ℂ → ℂ} {c : ℕ → ℂ} {n k : ℕ} (hk : k < n)
    (hq : Tendsto (fun x => ‖deriv Φ (t x)‖) l atTop)
    (hB : ∀ j < n, Tendsto (fun x => B j (t x) / deriv Φ (t x) ^ (n - j)) l (𝓝 (c j)))
    (hC : ∀ m ≤ n, ∀ j, (fun x => ExactChange.chainCoeff (deriv Φ) m j (t x)) =O[l]
      (fun x => deriv Φ (t x) ^ j)) :
    Tendsto (fun x => ExactChange.phaseCoeff n B Φ k (t x)) l (𝓝 (c k)) := by
  have hlead := chain_quotient_zero hk hq (hC n le_rfl k)
  have hterms : ∀ j ∈ Finset.range n, Tendsto
      (fun x => B j (t x) * ExactChange.chainCoeff (deriv Φ) j k (t x) /
        deriv Φ (t x) ^ n) l (𝓝 (if j = k then c k else 0)) := by
    intro j hj
    have hjn := Finset.mem_range.mp hj
    exact normalized_chain_term_limit hjn hq (hB j hjn) (hC j hjn.le k)
  have hsum := tendsto_finsetSum (Finset.range n) hterms
  have ht := hlead.add hsum
  have hv : (∑ j ∈ Finset.range n, if j = k then c k else 0) = c k := by
    simp [Finset.mem_range.mpr hk]
  rw [hv, zero_add] at ht
  convert ht using 1
  funext x
  unfold ExactChange.phaseCoeff
  simp only [div_eq_mul_inv, add_mul, Finset.sum_mul]

/-- The manuscript's reduced equation requires normalized limits only through
order `n-2`; the absent order `n-1` coefficient supplies its zero limit directly. -/
theorem phaseCoeff_limit_reduced {α : Type*} {l : Filter α} {t : α → ℂ}
    {Φ : ℂ → ℂ} {B : ℕ → ℂ → ℂ} {c : ℕ → ℂ} {n k : ℕ} (hk : k < n)
    (hq : Tendsto (fun x => ‖deriv Φ (t x)‖) l atTop)
    (hB : ∀ j < n - 1, Tendsto
      (fun x => B j (t x) / deriv Φ (t x) ^ (n - j)) l (𝓝 (c j)))
    (hred : ∀ᶠ x in l, B (n - 1) (t x) = 0) (hcred : c (n - 1) = 0)
    (hC : ∀ m ≤ n, ∀ j, (fun x => ExactChange.chainCoeff (deriv Φ) m j (t x)) =O[l]
      (fun x => deriv Φ (t x) ^ j)) :
    Tendsto (fun x => ExactChange.phaseCoeff n B Φ k (t x)) l (𝓝 (c k)) := by
  apply phaseCoeff_limit hk hq ?_ hC
  intro j hj
  by_cases hlow : j < n - 1
  · exact hB j hlow
  · have he : j = n - 1 := by omega
    subst j
    rw [hcred]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hred] with x hx
    simp [hx]

end
end ZeroDensity.PhaseCoefficientLimits
