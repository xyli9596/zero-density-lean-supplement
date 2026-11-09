import V10.PerronStableSubspaceForcing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The genuinely constructed fixed points form a linear initial-value graph
of precisely the stable-coordinate dimension. The differential-equation
identification is a separate calculus step. -/
noncomputable section
open Set Module
open scoped BoundedContinuousFunction
namespace V10.PerronStableSubspace
variable {ι : Type*} [Fintype ι]
variable (T δ η : ℝ) (hδ : 0 < δ) (hη : 0 ≤ η)
variable (mode : ι → Bool) (lam : ι → ℂ)
variable (hgap : ∀ i, if mode i then (lam i).re ≤ -δ else δ ≤ (lam i).re)
variable (R : Ici T → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hR : Continuous R)
variable (hsmallR : ∀ s, ‖R s‖ ≤ η) (hsmall : decayMass δ * η < 1)

def fixedPoint (v : ι → ℂ) : Ici T →ᵇ (ι → ℂ) :=
  Classical.choose (exists_unique_stable_fixed_point T δ η hδ hη mode lam hgap R hR hsmallR hsmall v)

lemma fixedPoint_spec (v : ι → ℂ) :
    fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall v =
      forcing T δ hδ mode lam hgap v + integralOperator T δ η hδ hη mode lam hgap R hR hsmallR
        (fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall v) :=
  (Classical.choose_spec (exists_unique_stable_fixed_point T δ η hδ hη mode lam hgap R hR hsmallR hsmall v)).1

lemma fixedPoint_unique (v : ι → ℂ) (u : Ici T →ᵇ (ι → ℂ))
    (hu : u = forcing T δ hδ mode lam hgap v +
      integralOperator T δ η hδ hη mode lam hgap R hR hsmallR u) :
    u = fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall v :=
  (Classical.choose_spec (exists_unique_stable_fixed_point T δ η hδ hη mode lam hgap R hR hsmallR hsmall v)).2 u hu

/-- Linearity follows from the proved uniqueness, not an assumed solution map. -/
def fixedPointLinear : (ι → ℂ) →ₗ[ℂ] (Ici T →ᵇ (ι → ℂ)) where
  toFun := fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall
  map_add' u v := by
    symm
    apply fixedPoint_unique T δ η hδ hη mode lam hgap R hR hsmallR hsmall
    change _ = forcingLinear T δ hδ mode lam hgap (u + v) +
      integralLinear T δ η hδ hη mode lam hgap R hR hsmallR (_ + _)
    rw [map_add, map_add]
    change _ = (forcing T δ hδ mode lam hgap u + forcing T δ hδ mode lam hgap v) +
      (integralOperator T δ η hδ hη mode lam hgap R hR hsmallR _ +
        integralOperator T δ η hδ hη mode lam hgap R hR hsmallR _)
    calc
      _ = (forcing T δ hδ mode lam hgap u +
          integralOperator T δ η hδ hη mode lam hgap R hR hsmallR
            (fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall u)) +
          (forcing T δ hδ mode lam hgap v +
          integralOperator T δ η hδ hη mode lam hgap R hR hsmallR
            (fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall v)) :=
        congrArg₂ (· + ·)
          (fixedPoint_spec T δ η hδ hη mode lam hgap R hR hsmallR hsmall u)
          (fixedPoint_spec T δ η hδ hη mode lam hgap R hR hsmallR hsmall v)
      _ = _ := by abel
  map_smul' c v := by
    symm
    apply fixedPoint_unique T δ η hδ hη mode lam hgap R hR hsmallR hsmall
    change _ = forcingLinear T δ hδ mode lam hgap (c • v) +
      integralLinear T δ η hδ hη mode lam hgap R hR hsmallR (c • _)
    rw [map_smul, map_smul]
    change c • fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall v =
      c • forcing T δ hδ mode lam hgap v +
        c • integralOperator T δ η hδ hη mode lam hgap R hR hsmallR
          (fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall v)
    calc
      _ = c • (forcing T δ hδ mode lam hgap v +
          integralOperator T δ η hδ hη mode lam hgap R hR hsmallR
            (fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall v)) :=
        congrArg (fun w : Ici T →ᵇ (ι → ℂ) => c • w)
          (fixedPoint_spec T δ η hδ hη mode lam hgap R hR hsmallR hsmall v)
      _ = _ := by
        ext r i
        simp only [BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.add_apply,
          Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        exact mul_add c _ _

/-- Stable parameters, extended by zero on the unstable coordinates. -/
def liftStable : ({i : ι // mode i = true} → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun v i := if h : mode i = true then v ⟨i,h⟩ else 0
  map_add' u v := by
    ext i
    by_cases hi : mode i = true <;> simp [hi]
  map_smul' c v := by
    ext i
    by_cases hi : mode i = true <;> simp [hi]

omit [Fintype ι] in
lemma liftStable_apply (v : {i : ι // mode i = true} → ℂ) (i : {i : ι // mode i = true}) :
    liftStable mode v i.val = v i := by simp [liftStable, i.property]

def initialGraphMap : ({i : ι // mode i = true} → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  ({ toFun := fun u : Ici T →ᵇ (ι → ℂ) => u ⟨T, by exact le_refl T⟩
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : (Ici T →ᵇ (ι → ℂ)) →ₗ[ℂ] (ι → ℂ)).comp
    ((fixedPointLinear T δ η hδ hη mode lam hgap R hR hsmallR hsmall).comp (liftStable mode))

theorem initialGraphMap_stable (v : {i : ι // mode i = true} → ℂ)
    (i : {i : ι // mode i = true}) :
    initialGraphMap T δ η hδ hη mode lam hgap R hR hsmallR hsmall v i.val = v i := by
  change fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall
    (liftStable mode v) ⟨T, by exact le_refl T⟩ i.val = _
  rw [fixed_point_initial_stable T δ η hδ hη mode lam hgap R hR hsmallR
    (liftStable mode v) _ (fixedPoint_spec T δ η hδ hη mode lam hgap R hR hsmallR hsmall _) i.val i.property]
  exact liftStable_apply mode v i

theorem initialGraphMap_injective : Function.Injective
    (initialGraphMap T δ η hδ hη mode lam hgap R hR hsmallR hsmall) := by
  intro u v huv
  funext i
  have hh := congrArg (fun w : ι → ℂ => w i.val) huv
  simpa only [initialGraphMap_stable] using hh

def initialGraph : Submodule ℂ (ι → ℂ) :=
  LinearMap.range (initialGraphMap T δ η hδ hη mode lam hgap R hR hsmallR hsmall)

/-- Exact dimension of the actual mixed fixed-point initial graph. -/
theorem finrank_initialGraph :
    finrank ℂ (initialGraph T δ η hδ hη mode lam hgap R hR hsmallR hsmall) =
      Fintype.card {i : ι // mode i = true} := by
  unfold initialGraph
  rw [LinearMap.finrank_range_of_inj
    (initialGraphMap_injective T δ η hδ hη mode lam hgap R hR hsmallR hsmall)]
  simp

#print axioms fixedPointLinear
#print axioms initialGraphMap_injective
#print axioms finrank_initialGraph
end V10.PerronStableSubspace
