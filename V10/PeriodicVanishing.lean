import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Finite tests for all-integer monodromy vanishing

This is the Cayley--Hamilton/invertibility step in v10 Proposition 7.4.
It does not prove the density-zero lower bound for nonvanishing sequences,
periodic coefficient asymptotics, or the full exceptional-set classification.
-/

open Polynomial
open scoped BigOperators

namespace V10.PeriodicVanishing
noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Cayley--Hamilton makes the first `dim V` tests sufficient for every
nonnegative power; the observation map may be vector-valued. -/
theorem first_powers_vanish_all_nat (A : V →ₗ[ℂ] V) (L : V →ₗ[ℂ] W) (c : V)
    (h : ∀ k : ℕ, k < Module.finrank ℂ V → L ((A ^ k) c) = 0) :
    ∀ k : ℕ, L ((A ^ k) c) = 0 := by
  intro k
  rw [A.pow_eq_aeval_mod_charpoly k]
  let p : Polynomial ℂ := X ^ k %ₘ A.charpoly
  change L ((aeval A p) c) = 0
  by_cases hp : p = 0
  · simp [hp]
  have hd : p.natDegree < Module.finrank ℂ V := by
    rw [← A.charpoly_natDegree]
    exact natDegree_lt_natDegree hp (degree_modByMonic_lt _ A.charpoly_monic)
  rw [aeval_eq_sum_range' hd A]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j hj
  rw [h j (Finset.mem_range.mp hj), smul_zero]

omit [FiniteDimensional ℂ V] in
lemma end_pow_apply_eq (A : V ≃ₗ[ℂ] V) (k : ℕ) (c : V) :
    ((A.toLinearMap ^ k) c) = (A ^ k) c := by
  simp only [Module.End.pow_apply, LinearEquiv.pow_apply]
  rfl

/-- The subspace annihilated by all forward observations. -/
def forwardSpace (A : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W) : Submodule ℂ V where
  carrier := {c | ∀ k : ℕ, L ((A ^ k) c) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd k
    simp only [map_add, hc k, hd k, add_zero]
  smul_mem' := by
    intro a c hc k
    simp only [map_smul, hc k, smul_zero]

omit [FiniteDimensional ℂ V] in
@[simp] lemma mem_forwardSpace (A : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W) (c : V) :
    c ∈ forwardSpace A L ↔ ∀ k : ℕ, L ((A ^ k) c) = 0 := Iff.rfl

omit [FiniteDimensional ℂ V] in
lemma map_mem_forwardSpace (A : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W)
    {c : V} (hc : c ∈ forwardSpace A L) : A c ∈ forwardSpace A L := by
  intro k
  simpa only [pow_succ, LinearEquiv.mul_apply] using hc (k + 1)

/-- On a finite-dimensional invariant subspace, an injective map is onto.
This proves backward invariance; it is not assumed as a premise. -/
theorem inv_mem_forwardSpace (A : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W)
    {c : V} (hc : c ∈ forwardSpace A L) : A⁻¹ c ∈ forwardSpace A L := by
  let F : forwardSpace A L →ₗ[ℂ] forwardSpace A L :=
    { toFun := fun x ↦ ⟨A x.val, map_mem_forwardSpace A L x.property⟩
      map_add' := by intro x y; apply Subtype.ext; exact A.map_add x.val y.val
      map_smul' := by intro a x; apply Subtype.ext; exact A.map_smul a x.val }
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    apply A.injective
    exact congrArg Subtype.val hxy
  obtain ⟨d, hd⟩ := LinearMap.surjective_of_injective hinj ⟨c, hc⟩
  have heq : A d.val = c := congrArg Subtype.val hd
  have hi : A⁻¹ c = d.val := by
    rw [← heq]
    exact A.symm_apply_apply d.val
  rw [hi]
  exact d.property

theorem integer_powers_mem_forwardSpace (A : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W)
    {c : V} (hc : c ∈ forwardSpace A L) (k : ℤ) :
    (A ^ k) c ∈ forwardSpace A L := by
  have hpos : ∀ n : ℕ, (A ^ n) c ∈ forwardSpace A L := by
    intro n
    induction n with
    | zero => simpa using hc
    | succ n ih =>
        simpa only [pow_succ', LinearEquiv.mul_apply] using map_mem_forwardSpace A L ih
  have hneg : ∀ n : ℕ, ((A⁻¹) ^ n) c ∈ forwardSpace A L := by
    intro n
    induction n with
    | zero => simpa using hc
    | succ n ih =>
        simpa only [pow_succ', LinearEquiv.mul_apply] using inv_mem_forwardSpace A L ih
  cases k with
  | ofNat n => convert hpos n using 1; rfl
  | negSucc n => simpa only [zpow_negSucc, ← inv_pow] using hneg (n + 1)

/-- The exact all-integer finite-test equivalence, including negative powers
and the zero-dimensional case. -/
theorem first_powers_iff_all_integer (A : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W) (c : V) :
    (∀ k : ℕ, k < Module.finrank ℂ V → L ((A ^ k) c) = 0) ↔
      ∀ k : ℤ, L ((A ^ k) c) = 0 := by
  constructor
  · intro h
    have hf : c ∈ forwardSpace A L := by
      intro k
      have hn := first_powers_vanish_all_nat A.toLinearMap L c
        (fun j hj ↦ by simpa only [end_pow_apply_eq] using h j hj) k
      simpa only [end_pow_apply_eq] using hn
    intro k
    have hz := integer_powers_mem_forwardSpace A L hf k
    simpa using hz 0
  · intro h k hk
    simpa only [zpow_natCast] using h (k : ℤ)

/-- The finite intersection printed in the manuscript. -/
def finiteVanishingSpace (A : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W) : Submodule ℂ V :=
  ⨅ k : Fin (Module.finrank ℂ V), LinearMap.ker (L.comp (A ^ k.val).toLinearMap)

/-- Vanishing for all integer iterates. -/
def integerVanishingSpace (A : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W) : Submodule ℂ V :=
  ⨅ k : ℤ, LinearMap.ker (L.comp (A ^ k).toLinearMap)

theorem finiteVanishingSpace_eq_integer (A : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W) :
    finiteVanishingSpace A L = integerVanishingSpace A L := by
  ext c
  simp only [finiteVanishingSpace, integerVanishingSpace, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe]
  constructor
  · intro h
    apply (first_powers_iff_all_integer A L c).mp
    intro k hk
    exact h ⟨k, hk⟩
  · intro h k
    exact (first_powers_iff_all_integer A L c).mpr h k.val k.isLt

/-- Nonzero block projections give proper finite-test subspaces. -/
theorem finiteVanishingSpace_ne_top (A : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W) (hL : L ≠ 0) :
    finiteVanishingSpace A L ≠ ⊤ := by
  intro ht
  apply hL
  ext c
  change L c = 0
  have hc : c ∈ finiteVanishingSpace A L := by rw [ht]; exact Submodule.mem_top
  rw [finiteVanishingSpace_eq_integer] at hc
  have hh : ∀ k : ℤ, L ((A ^ k) c) = 0 := by
    simpa only [integerVanishingSpace, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using hc
  simpa using hh 0

omit [FiniteDimensional ℂ V] in
lemma progression_apply (M : V ≃ₗ[ℂ] V) (h N k : ℤ) (c : V) :
    ((M ^ N) ^ k) ((M ^ h) c) = (M ^ (h + N * k)) c := by
  rw [← zpow_mul, ← LinearEquiv.mul_apply, ← zpow_add, add_comm (N * k) h]

/-- The finite-test criterion for every arithmetic progression of monodromy
iterates. It holds for all integer `h,N`, hence in particular for the paper's
`N ≥ 1` and `0 ≤ h < N`. -/
theorem progression_first_iff_all_integer (M : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W)
    (h N : ℤ) (c : V) :
    (∀ k : ℕ, k < Module.finrank ℂ V → L ((M ^ (h + N * (k : ℤ))) c) = 0) ↔
      ∀ k : ℤ, L ((M ^ (h + N * k)) c) = 0 := by
  have hnat (k : ℕ) : ((M ^ N) ^ k) ((M ^ h) c) = (M ^ (h + N * (k : ℤ))) c := by
    simpa only [zpow_natCast] using progression_apply M h N (k : ℤ) c
  constructor
  · intro hf
    have hh : ∀ k : ℕ, k < Module.finrank ℂ V →
        L (((M ^ N) ^ k) ((M ^ h) c)) = 0 := by
      intro k hk
      rw [hnat]
      exact hf k hk
    have hall := (first_powers_iff_all_integer (M ^ N) L ((M ^ h) c)).mp hh
    intro k
    rw [← progression_apply]
    exact hall k
  · intro hall k _
    exact hall (k : ℤ)

/-- The exact finite intersection in equation `periodic-vanishing-spaces`. -/
def residueFiniteSpace (M : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W) (h N : ℤ) : Submodule ℂ V :=
  ⨅ k : Fin (Module.finrank ℂ V),
    LinearMap.ker (L.comp (M ^ (h + N * (k.val : ℤ))).toLinearMap)

/-- The corresponding all-integer vanishing subspace. -/
def residueIntegerSpace (M : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W) (h N : ℤ) : Submodule ℂ V :=
  ⨅ k : ℤ, LinearMap.ker (L.comp (M ^ (h + N * k)).toLinearMap)

theorem residueFiniteSpace_eq_integer (M : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W) (h N : ℤ) :
    residueFiniteSpace M L h N = residueIntegerSpace M L h N := by
  ext c
  simp only [residueFiniteSpace, residueIntegerSpace, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe]
  constructor
  · intro hf
    apply (progression_first_iff_all_integer M L h N c).mp
    intro k hk
    exact hf ⟨k, hk⟩
  · intro hall k
    exact hall (k.val : ℤ)

/-- Every nonzero block observation gives a proper residue vanishing space.
No spectral simplicity, rank-one observation, or simple eigenvalues are used. -/
theorem residueFiniteSpace_ne_top (M : V ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] W)
    (hL : L ≠ 0) (h N : ℤ) : residueFiniteSpace M L h N ≠ ⊤ := by
  intro ht
  apply hL
  ext v
  change L v = 0
  obtain ⟨c, rfl⟩ := (M ^ h).surjective v
  have hc : c ∈ residueFiniteSpace M L h N := by rw [ht]; exact Submodule.mem_top
  rw [residueFiniteSpace_eq_integer] at hc
  have hh : ∀ k : ℤ, L ((M ^ (h + N * k)) c) = 0 := by
    simpa only [residueIntegerSpace, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using hc
  simpa only [mul_zero, add_zero] using hh 0

end
end V10.PeriodicVanishing
