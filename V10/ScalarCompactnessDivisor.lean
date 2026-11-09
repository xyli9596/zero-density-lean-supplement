import V10.ScalarCompactnessJensen

/-!
# L¹ compactness of actual normalized analytic divisor potentials

Unlike an assumed mass bound, the mass estimate here is obtained by Jensen's
inequality from actual analytic upper and lower bounds. The number and location
of zeros may vary arbitrarily, including collisions and growing multiplicities.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace V10.ScalarCompactnessDivisor
open ScalarCompactnessLogPotential ScalarCompactnessJensen

def divisorSupport (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor f (closedBall c r)).finiteSupport
    (isCompact_closedBall c r)).toFinset

theorem mem_divisorSupport {f : ℂ → ℂ} {c z : ℂ} {r : ℝ} :
    z ∈ divisorSupport f c r ↔ MeromorphicOn.divisor f (closedBall c r) z ≠ 0 := by
  simp [divisorSupport, Function.mem_support]

theorem divisorSupport_subset (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    (divisorSupport f c r : Set ℂ) ⊆ closedBall c r := by
  intro z hz
  exact (MeromorphicOn.divisor f (closedBall c r)).supportWithinDomain
    (mem_divisorSupport.mp hz)

theorem divisor_sum_eq (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    ∑ᶠ u, MeromorphicOn.divisor f (closedBall c r) u =
      ∑ u ∈ divisorSupport f c r, MeromorphicOn.divisor f (closedBall c r) u := by
  apply finsum_eq_sum_of_support_subset
  intro z hz
  exact mem_divisorSupport.mpr hz

def divisorPotential (f : ℂ → ℂ) (c : ℂ) (r q cutoff : ℝ) : L1 :=
  ∑ u ∈ divisorSupport f c r,
    ((MeromorphicOn.divisor f (closedBall c r) u : ℝ) / q) • logKernelL1 cutoff u

/-- The mass-bound interface for the actual analytic divisor. The bound can
be supplied by Jensen at a different (possibly moving) center. -/
theorem divisor_potential_tendsto_subseq_of_mass_bound
    {f : ℕ → ℂ → ℂ} {q : ℕ → ℝ} {c : ℂ} {r M cutoff : ℝ}
    (hq : ∀ n, 0 < q n) (hM : 0 < M)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c r))
    (hmass : ∀ n, ∑ u ∈ divisorSupport (f n) c r,
      (MeromorphicOn.divisor (f n) (closedBall c r) u : ℝ) / q n ≤ M) :
    ∃ u : L1, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => divisorPotential (f (σ n)) c r (q (σ n)) cutoff)
        atTop (𝓝 u) := by
  classical
  let κ : ℕ → Type := fun n => {z // z ∈ divisorSupport (f n) c r}
  let a : ∀ n, κ n → ℂ := fun _ z => z.val
  let w : ∀ n, κ n → ℝ := fun n z =>
    (MeromorphicOn.divisor (f n) (closedBall c r) z : ℝ) / q n
  have hw : ∀ n i, 0 ≤ w n i := by
    intro n i
    apply div_nonneg _ (hq n).le
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf n) i
  have hs : ∀ n, ∑ i, w n i ≤ M := by
    intro n
    change (∑ i : {z // z ∈ divisorSupport (f n) c r},
      (MeromorphicOn.divisor (f n) (closedBall c r) i : ℝ) / q n) ≤ M
    rw [Finset.sum_coe_sort (divisorSupport (f n) c r)
      (fun z => (MeromorphicOn.divisor (f n) (closedBall c r) z : ℝ) / q n)]
    exact hmass n
  have ha : ∀ n i, a n i ∈ closedBall c r := fun n i =>
    divisorSupport_subset (f n) c r i.property
  obtain ⟨u, σ, hσ, hu⟩ := logPotential_tendsto_subseq
    (κ := κ) (R := cutoff) (isCompact_closedBall c r) hM hw hs ha
  refine ⟨u, σ, hσ, ?_⟩
  convert hu using 1
  funext n
  exact (Finset.sum_coe_sort (divisorSupport (f (σ n)) c r)
    (fun z => ((MeromorphicOn.divisor (f (σ n)) (closedBall c r) z : ℝ) / q (σ n)) •
      logKernelL1 cutoff z)).symm

theorem normalized_divisor_sum_le {f : ℂ → ℂ} {c : ℂ} {r R q B C : ℝ}
    (hr : 0 < r) (hrR : r < R) (hq : 0 < q) (hB : 0 ≤ B)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hupper : ∀ z ∈ sphere c R, ‖f z‖ ≤ Real.exp (q * B))
    (hlower : Real.exp (-q * C) ≤ ‖f c‖) :
    ∑ u ∈ divisorSupport f c r,
      (MeromorphicOn.divisor f (closedBall c r) u : ℝ) / q ≤
      (B + C) / Real.log (R / r) := by
  have he : (∑ u ∈ divisorSupport f c r,
      (MeromorphicOn.divisor f (closedBall c r) u : ℝ) / q) =
      ((∑ᶠ u, MeromorphicOn.divisor f (closedBall c r) u : ℤ) : ℝ) / q := by
    rw [divisor_sum_eq, Int.cast_sum, Finset.sum_div]
  rw [he]
  exact normalized_divisor_mass_le hr hrR hq hB hf hupper hlower

/-- A complete, unconditional compactness statement for the actual divisor
part of normalized analytic logarithms on a disk. The positive mass bound is
derived from the stated analytic norm bounds, not supplied as a premise. -/
theorem analytic_divisor_potential_tendsto_subseq
    {f : ℕ → ℂ → ℂ} {q : ℕ → ℝ} {c : ℂ} {r R B C cutoff : ℝ}
    (hr : 0 < r) (hrR : r < R) (hq : ∀ n, 0 < q n) (hB : 0 ≤ B)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hupper : ∀ n z, z ∈ sphere c R → ‖f n z‖ ≤ Real.exp (q n * B))
    (hlower : ∀ n, Real.exp (-q n * C) ≤ ‖f n c‖) :
    ∃ u : L1, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => divisorPotential (f (σ n)) c r (q (σ n)) cutoff)
        atTop (𝓝 u) := by
  classical
  let κ : ℕ → Type := fun n => {z // z ∈ divisorSupport (f n) c r}
  let a : ∀ n, κ n → ℂ := fun _ z => z.val
  let w : ∀ n, κ n → ℝ := fun n z =>
    (MeromorphicOn.divisor (f n) (closedBall c r) z : ℝ) / q n
  let M := 1 + max 0 ((B + C) / Real.log (R / r))
  have hM : 0 < M := by dsimp [M]; positivity
  have hw : ∀ n i, 0 ≤ w n i := by
    intro n i
    apply div_nonneg _ (hq n).le
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      ((hf n).mono (closedBall_subset_closedBall hrR.le)) i
  have hs : ∀ n, ∑ i, w n i ≤ M := by
    intro n
    change (∑ i : {z // z ∈ divisorSupport (f n) c r},
      (MeromorphicOn.divisor (f n) (closedBall c r) i : ℝ) / q n) ≤ M
    rw [Finset.sum_coe_sort (divisorSupport (f n) c r)
      (fun z => (MeromorphicOn.divisor (f n) (closedBall c r) z : ℝ) / q n)]
    have h := normalized_divisor_sum_le hr hrR (hq n) hB (hf n) (hupper n) (hlower n)
    exact h.trans (by dsimp [M]; linarith [le_max_right 0 ((B + C) / Real.log (R / r))])
  have ha : ∀ n i, a n i ∈ closedBall c r := fun n i =>
    divisorSupport_subset (f n) c r i.property
  obtain ⟨u, σ, hσ, hu⟩ := logPotential_tendsto_subseq
    (κ := κ) (R := cutoff) (isCompact_closedBall c r) hM hw hs ha
  refine ⟨u, σ, hσ, ?_⟩
  convert hu using 1
  funext n
  exact (Finset.sum_coe_sort (divisorSupport (f (σ n)) c r)
    (fun z => ((MeromorphicOn.divisor (f (σ n)) (closedBall c r) z : ℝ) / q (σ n)) •
      logKernelL1 cutoff z)).symm

end V10.ScalarCompactnessDivisor
