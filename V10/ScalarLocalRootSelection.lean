import V10.LocalRootSupport
import V10.ScalarIndicatorLimit
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Lemma 3.3 for the actual scalar ODE

The limiting polynomial is built from the actual limiting coefficients. Its
distinct roots form a finite nonempty set by monicity, positive degree, and
the fundamental theorem of algebra. Lemma 3.2 supplies the actual solution's
subharmonic homogeneous indicator and its root alternatives. On any open
subinterval of the original angle domain having length less than π, the
proved support theorem gives the maximum and exact vertex assertions.
-/

noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace V10.ScalarLocalRootSelection
open ScalarIndicatorLimit LocalRootSupport SectorScaledNeighborhood PerronSector
open ZeroDensity.LocalRootSelection
set_option backward.isDefEq.respectTransparency false

def characteristicPolynomial {n : ℕ} (c : Fin n → ℂ) : Polynomial ℂ :=
  X ^ n + ∑ j : Fin n, C (c j) * X ^ j.val

theorem characteristicPolynomial_monic {n : ℕ} (c : Fin n → ℂ) :
    (characteristicPolynomial c).Monic :=
  Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c)

theorem characteristicPolynomial_natDegree {n : ℕ} (c : Fin n → ℂ) :
    (characteristicPolynomial c).natDegree = n := by
  unfold characteristicPolynomial
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  simpa only [degree_X_pow] using Polynomial.degree_sum_fin_lt c

theorem characteristicPolynomial_eval {n : ℕ} (c : Fin n → ℂ) (μ : ℂ) :
    (characteristicPolynomial c).eval μ = μ ^ n + ∑ j : Fin n, c j * μ ^ j.val := by
  simp [characteristicPolynomial, Polynomial.eval_finsetSum]

def characteristicRoots {n : ℕ} (c : Fin n → ℂ) : Finset ℂ :=
  (characteristicPolynomial c).roots.toFinset

theorem mem_characteristicRoots {n : ℕ} (c : Fin n → ℂ) (μ : ℂ) :
    μ ∈ characteristicRoots c ↔ μ ^ n + ∑ j : Fin n, c j * μ ^ j.val = 0 := by
  classical
  simp only [characteristicRoots, Multiset.mem_toFinset,
    Polynomial.mem_roots (characteristicPolynomial_monic c).ne_zero,
    Polynomial.IsRoot.def, characteristicPolynomial_eval]

theorem characteristicRoots_nonempty {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    (characteristicRoots c).Nonempty := by
  have hdeg : 0 < (characteristicPolynomial c).degree := by
    rw [Polynomial.degree_eq_natDegree (characteristicPolynomial_monic c).ne_zero,
      characteristicPolynomial_natDegree]
    exact_mod_cast hn
  obtain ⟨μ, hμ⟩ := Complex.exists_root hdeg
  exact ⟨μ, (mem_characteristicRoots c μ).mpr
    (by rwa [← characteristicPolynomial_eval])⟩

/-- Current manuscript Lemma 3.3, from the original scalar ODE assumptions
of Lemma 3.2. The counting interval `Ioo l u` is only required to lie inside
the original general open connected angle domain `J₀`. -/
theorem lemma_3_3 {n : ℕ} {v : ℂ → ℂ} {b : ℂ → Fin (n + 1) → ℂ}
    {c : Fin (n + 1) → ℂ} {R₀ : ℝ} {J₀ : Set ℝ}
    (hR₀ : 0 < R₀) (hJo : IsOpen J₀) (hJc : IsPreconnected J₀)
    (hv : AnalyticOnNhd ℂ v (sector R₀ J₀))
    (hb : ContinuousOn b (sector R₀ J₀))
    (hscalar : ∀ z ∈ sector R₀ J₀, iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0)
    (hnontrivial : ∃ z ∈ sector R₀ J₀, v z ≠ 0)
    (hlim : ∀ j (K : Set ℝ), K ⊆ J₀ → IsCompact K →
      TendstoUniformlyOn
        (fun r : ℝ => fun θ : ℝ => b ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) j)
        (fun _ => c j) atTop K)
    {l u : ℝ} (hlu : l < u) (hshort : u - l < Real.pi) (hJsub : Ioo l u ⊆ J₀) :
    ∃ hne : (selected (characteristicRoots c) (angularIndicator v) l u).Nonempty,
      (∀ θ ∈ Ioo l u, angularIndicator v θ =
        (selected (characteristicRoots c) (angularIndicator v) l u).sup' hne
          (fun μ => projection μ θ)) ∧
      (convexHull ℝ
        (((selected (characteristicRoots c) (angularIndicator v) l u).image star : Finset ℂ) :
          Set ℂ)).extremePoints ℝ =
        (((selected (characteristicRoots c) (angularIndicator v) l u).image star : Finset ℂ) :
          Set ℂ) := by
  obtain ⟨_, hSH, _, hroots, hcont, hhom⟩ :=
    ScalarIndicatorLimit.lemma_3_2 hR₀ hJo hJc hv hb hscalar hnontrivial hlim
  have hcone : fullCone (Ioo l u) ⊆ fullCone J₀ := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨w, hJsub hw, rfl⟩
  refine LocalRootSupport.local_root_selection (characteristicRoots c) hlu hshort
    (hSH.mono hcone) ?_ (hcont.mono hJsub) ?_
  · intro θ hθ r hr
    change homogeneousIndicator v ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = _
    exact hhom θ (hJsub hθ) r hr
  · intro θ hθ
    obtain ⟨μ, hμ, _, he⟩ := hroots _ (unit_ray_mem_fullCone (hJsub hθ))
    refine ⟨μ, (mem_characteristicRoots c μ).mpr hμ, ?_⟩
    rw [projection_eq]
    exact he

#print axioms characteristicRoots_nonempty
#print axioms lemma_3_3
end V10.ScalarLocalRootSelection
