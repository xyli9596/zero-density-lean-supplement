import V10.PerronSpectralJordan

/-! Quantitative Euclidean energy bounds from actual matrix entries. -/
noncomputable section
open Module Complex
open scoped BigOperators ComplexConjugate Matrix
namespace V10.PerronSpectral

/-- Squared Euclidean norm, written as a coordinate sum to avoid norm-instance choices. -/
def energy {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

def quadraticReal {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) (x : ι → ℂ) : ℝ :=
  ∑ i, (conj (x i) * (B *ᵥ x) i).re

lemma energy_nonneg {ι : Type*} [Fintype ι] (x : ι → ℂ) : 0 ≤ energy x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma abs_re_triple_le (x b y : ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hb : ‖b‖ ≤ ε) :
    |(conj x * (b * y)).re| ≤ ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  calc
    _ ≤ ‖conj x * (b * y)‖ := Complex.abs_re_le_norm _
    _ = ‖x‖ * ‖b‖ * ‖y‖ := by simp [mul_assoc]
    _ ≤ ‖x‖ * ε * ‖y‖ := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hε (sq_nonneg (‖x‖ - ‖y‖))]

/-- An entrywise-small matrix gives a proved quadratic-form bound. The dimension
factor is deliberately retained; it can be absorbed by the Jordan rescaling. -/
theorem abs_quadraticReal_le {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℂ) (x : ι → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hB : ∀ i j, ‖B i j‖ ≤ ε) :
    |quadraticReal B x| ≤ ε * Fintype.card ι * energy x := by
  classical
  have heq : quadraticReal B x = ∑ i, ∑ j, (conj (x i) * (B i j * x j)).re := by
    simp only [quadraticReal, Matrix.mulVec, dotProduct, Finset.mul_sum, Complex.re_sum]
  rw [heq]
  calc
    _ ≤ ∑ i, ∑ j, |(conj (x i) * (B i j * x j)).re| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, ε * (‖x i‖ ^ 2 + ‖x j‖ ^ 2) / 2 := by
      gcongr with i hi j hj
      exact abs_re_triple_le _ _ _ ε hε (hB i j)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        energy]
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring

lemma quadraticReal_add {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadraticReal (B + C) x = quadraticReal B x + quadraticReal C x := by
  simp [quadraticReal, Matrix.add_mulVec, mul_add, Finset.sum_add_distrib]

lemma quadraticReal_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam x : ι → ℂ) :
    quadraticReal (Matrix.diagonal lam) x = ∑ i, (lam i).re * ‖x i‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mulVec_diagonal]
  have he : conj (x i) * (lam i * x i) = lam i * (conj (x i) * x i) := by ring
  rw [he, ← Complex.normSq_eq_conj_mul_self, Complex.mul_re]
  rw [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.normSq_eq_norm_sq]

/-- Upper and lower numerical-range control without a diagonalizability assumption. -/
theorem quadraticReal_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℂ) (B : Matrix ι ι ℂ) (x : ι → ℂ) (α ε : ℝ)
    (hε : 0 ≤ ε) (hlam : ∀ i, (lam i).re ≤ α) (hB : ∀ i j, ‖B i j‖ ≤ ε) :
    quadraticReal (Matrix.diagonal lam + B) x ≤
      (α + ε * Fintype.card ι) * energy x := by
  rw [quadraticReal_add, quadraticReal_diagonal]
  have hd : (∑ i, (lam i).re * ‖x i‖ ^ 2) ≤ α * energy x := by
    rw [energy, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlam i) (sq_nonneg _)
  have hb := (le_abs_self (quadraticReal B x)).trans (abs_quadraticReal_le B x ε hε hB)
  nlinarith

/-- The energy of an actual coordinate block. -/
def blockEnergy {ι : Type*} (s : Finset ι) (x : ι → ℂ) : ℝ :=
  ∑ i ∈ s, ‖x i‖ ^ 2

def blockQuadratic {ι : Type*} [Fintype ι] (s : Finset ι)
    (B : Matrix ι ι ℂ) (x : ι → ℂ) : ℝ :=
  ∑ i ∈ s, (conj (x i) * (B *ᵥ x) i).re

lemma blockEnergy_nonneg {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    0 ≤ blockEnergy s x := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Block estimate uses the proved zero cross-block entries, so no outside
coordinate enters its right-hand side. -/
theorem abs_blockQuadratic_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (B : Matrix ι ι ℂ) (x : ι → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hB : ∀ i j, ‖B i j‖ ≤ ε)
    (hcross : ∀ i ∈ s, ∀ j ∉ s, B i j = 0) :
    |blockQuadratic s B x| ≤ ε * s.card * blockEnergy s x := by
  have heq : blockQuadratic s B x =
      ∑ i ∈ s, ∑ j ∈ s, (conj (x i) * (B i j * x j)).re := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Complex.re_sum]
    exact (Finset.sum_subset (Finset.subset_univ s) (fun j _ hj => by
      simp [hcross i hi j hj])).symm
  rw [heq]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, |(conj (x i) * (B i j * x j)).re| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ε * (‖x i‖ ^ 2 + ‖x j‖ ^ 2) / 2 := by
      gcongr with i hi j hj
      exact abs_re_triple_le _ _ _ ε hε (hB i j)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, blockEnergy]
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring

lemma blockQuadratic_diagonal_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (lam : ι → ℂ) (B : Matrix ι ι ℂ) (x : ι → ℂ) :
    blockQuadratic s (Matrix.diagonal lam + B) x =
      (∑ i ∈ s, (lam i).re * ‖x i‖ ^ 2) + blockQuadratic s B x := by
  simp only [blockQuadratic, Matrix.add_mulVec, Pi.add_apply, mul_add, Complex.add_re,
    Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mulVec_diagonal]
  have he : conj (x i) * (lam i * x i) = lam i * (conj (x i) * x i) := by ring
  rw [he, ← Complex.normSq_eq_conj_mul_self, Complex.mul_re]
  rw [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.normSq_eq_norm_sq]

theorem blockQuadratic_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (lam : ι → ℂ) (B : Matrix ι ι ℂ) (x : ι → ℂ) (α ε : ℝ)
    (hε : 0 ≤ ε) (hlam : ∀ i ∈ s, (lam i).re ≤ α) (hB : ∀ i j, ‖B i j‖ ≤ ε)
    (hcross : ∀ i ∈ s, ∀ j ∉ s, B i j = 0) :
    blockQuadratic s (Matrix.diagonal lam + B) x ≤
      (α + ε * s.card) * blockEnergy s x := by
  rw [blockQuadratic_diagonal_add]
  have hd : (∑ i ∈ s, (lam i).re * ‖x i‖ ^ 2) ≤ α * blockEnergy s x := by
    rw [blockEnergy, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hlam i hi) (sq_nonneg _)
  have hb := (le_abs_self (blockQuadratic s B x)).trans
    (abs_blockQuadratic_le s B x ε hε hB hcross)
  nlinarith

theorem le_blockQuadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (lam : ι → ℂ) (B : Matrix ι ι ℂ) (x : ι → ℂ) (α ε : ℝ)
    (hε : 0 ≤ ε) (hlam : ∀ i ∈ s, α ≤ (lam i).re) (hB : ∀ i j, ‖B i j‖ ≤ ε)
    (hcross : ∀ i ∈ s, ∀ j ∉ s, B i j = 0) :
    (α - ε * s.card) * blockEnergy s x ≤
      blockQuadratic s (Matrix.diagonal lam + B) x := by
  rw [blockQuadratic_diagonal_add]
  have hd : α * blockEnergy s x ≤ (∑ i ∈ s, (lam i).re * ‖x i‖ ^ 2) := by
    rw [blockEnergy, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hlam i hi) (sq_nonneg _)
  have hb := (neg_abs_le (blockQuadratic s B x)).trans' (neg_le_neg
    (abs_blockQuadratic_le s B x ε hε hB hcross))
  nlinarith

end V10.PerronSpectral
