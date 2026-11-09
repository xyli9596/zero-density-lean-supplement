import V10.PerronSpectralEnergy

/-! The terminal spectral-to-energy bridge for general complex operators.
The basis and the two strict energy estimates are constructed from the actual
spectrum; repeated eigenvalues and all Jordan blocks are allowed. -/
noncomputable section
open Module
namespace V10.PerronSpectral
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A spectral cut produces actual adapted finite coordinates and strict upper
and lower energy bounds. Neither estimate is a premise. -/
theorem exists_adapted_energy (A : End ℂ V) (γ : ℝ)
    (hγ : ∀ a : A.Eigenvalues, a.val.re ≠ γ) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
        (b : Basis ι ℂ V) (s : Finset ι),
        (∀ x : ι → ℂ, blockQuadratic s (LinearMap.toMatrix b b A) x ≤
          (γ - 2 * δ) * blockEnergy s x) ∧
        (∀ x : ι → ℂ, (γ + 2 * δ) * blockEnergy sᶜ x ≤
          blockQuadratic sᶜ (LinearMap.toMatrix b b A) x) := by
  classical
  obtain ⟨g, hg, hgap⟩ := exists_spectral_gap A γ hγ
  let n : ℝ := finrank ℂ V
  have hn : 0 < n + 1 := by dsimp [n]; positivity
  let ε : ℝ := g / (2 * (n + 1))
  have hε : 0 < ε := div_pos hg (mul_pos (by norm_num) hn)
  obtain ⟨ι, fι, dι, b, lam, N, hlam, hA, hN, hblock⟩ :=
    exists_small_remainder_basis A ε hε
  let _ := fι
  let _ := dι
  let s : Finset ι := Finset.univ.filter (fun i => (lam i).re < γ)
  have hcard : (Fintype.card ι : ℝ) = n := by
    dsimp [n]
    exact_mod_cast (Module.finrank_eq_card_basis b).symm
  have hsmall (t : Finset ι) : ε * t.card ≤ g / 2 := by
    have ht : (t.card : ℝ) ≤ n + 1 := by
      have hh : (t.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
        exact_mod_cast Finset.card_le_univ t
      rw [hcard] at hh
      linarith
    calc
      _ ≤ ε * (n + 1) := mul_le_mul_of_nonneg_left ht hε.le
      _ = g / 2 := by dsimp [ε]; field_simp
  have hsmem (i : ι) : i ∈ s ↔ (lam i).re < γ := by simp [s]
  have hsval : ∀ i ∈ s, (lam i).re ≤ γ - g := by
    intro i hi
    rcases hgap ⟨lam i, hlam i⟩ with h | h
    · exact h
    · have hh := (hsmem i).mp hi
      dsimp at h
      linarith
  have huval : ∀ i ∈ sᶜ, γ + g ≤ (lam i).re := by
    intro i hi
    have hh : ¬(lam i).re < γ := by simpa only [Finset.mem_compl, hsmem] using hi
    rcases hgap ⟨lam i, hlam i⟩ with h | h
    · dsimp at h
      linarith
    · exact h
  have hscross : ∀ i ∈ s, ∀ j ∉ s, N i j = 0 := by
    intro i hi j hj
    apply hblock
    intro hij
    apply hj
    apply (hsmem j).mpr
    rw [← hij]
    exact (hsmem i).mp hi
  have hucross : ∀ i ∈ sᶜ, ∀ j ∉ sᶜ, N i j = 0 := by
    intro i hi j hj
    apply hblock
    intro hij
    have hin : i ∉ s := Finset.mem_compl.mp hi
    have hjin : j ∈ s := by simpa using hj
    apply hin
    apply (hsmem i).mpr
    rw [hij]
    exact (hsmem j).mp hjin
  refine ⟨g / 4, by positivity, ι, fι, dι, b, s, ?_, ?_⟩
  · intro x
    rw [hA]
    have he := blockQuadratic_le s lam N x (γ - g) ε hε.le hsval hN hscross
    have hm := mul_le_mul_of_nonneg_right (hsmall s) (blockEnergy_nonneg s x)
    nlinarith
  · intro x
    rw [hA]
    have he := le_blockQuadratic sᶜ lam N x (γ + g) ε hε.le huval hN hucross
    have hm := mul_le_mul_of_nonneg_right (hsmall sᶜ) (blockEnergy_nonneg sᶜ x)
    nlinarith

end V10.PerronSpectral
