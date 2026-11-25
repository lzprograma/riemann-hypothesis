module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStA

@[expose] public section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

section Crd

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def crd {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) :
    V →ₗ[K] (Fin r → K) :=
  (Basis.span hli).equivFun.toLinearMap ∘ₗ
    (LinearMap.exists_leftInverse_of_injective (Submodule.span K (Set.range v)).subtype
      (Submodule.ker_subtype _)).choose

theorem crd_of_mem {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) {x : V}
    (hx : x ∈ Submodule.span K (Set.range v)) :
    crd hli x = (Basis.span hli).equivFun ⟨x, hx⟩ := by
  unfold crd
  have h := (LinearMap.exists_leftInverse_of_injective (Submodule.span K (Set.range v)).subtype
      (Submodule.ker_subtype _)).choose_spec
  have h2 : (LinearMap.exists_leftInverse_of_injective (Submodule.span K (Set.range v)).subtype
      (Submodule.ker_subtype _)).choose x = ⟨x, hx⟩ := by
    have := congrArg (fun f => f ⟨x, hx⟩) h
    simpa using this
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h2]

theorem sum_crd {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) {x : V}
    (hx : x ∈ Submodule.span K (Set.range v)) : ∑ i, crd hli x i • v i = x := by
  rw [crd_of_mem hli hx]
  have h := (Basis.span hli).sum_equivFun ⟨x, hx⟩
  have h2 := congrArg Subtype.val h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Basis.span_apply] at h2
  exact h2

end Crd

section Lat

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def crdEmb {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) :
    V →+ (Fin r → mixedEmbedding.mixedSpace K) where
  toFun x i := mixedEmbedding K (crd hli x i)
  map_zero' := by ext1 i; simp
  map_add' x y := by ext1 i; simp


variable (K) in
noncomputable def latB (r : ℕ) :
    Basis (Σ _ : Fin r, Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (Fin r → mixedEmbedding.mixedSpace K) :=
  Pi.basis fun _ => mixedEmbedding.latticeBasis K


variable (K) in
noncomputable def lat0 (r : ℕ) : Submodule ℤ (Fin r → mixedEmbedding.mixedSpace K) :=
  Submodule.span ℤ (Set.range (latB K r))

end Lat

end ReciprocityTheory.GeometryOfNumbersTheory

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

instance instMeasurableAddMixed : MeasurableAdd (mixedEmbedding.mixedSpace K) :=
  MeasurableAdd₂.toMeasurableAdd

instance instHaarPiMixed (r : ℕ) :
    (volume : Measure (Fin r → mixedEmbedding.mixedSpace K)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

instance instBorelPiMixed (r : ℕ) :
    @BorelSpace (Fin r → mixedEmbedding.mixedSpace K) _ MeasureSpace.toMeasurableSpace :=
  Pi.borelSpace

instance (r : ℕ) : DiscreteTopology (lat0 K r) := by unfold lat0; infer_instance

instance (r : ℕ) : IsZLattice ℝ (lat0 K r) := by unfold lat0; infer_instance

noncomputable def latE {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v)
    (E : Submodule (𝓞 K) V) : Submodule ℤ (Fin r → mixedEmbedding.mixedSpace K) :=
  (E.toAddSubgroup.map (crdEmb hli)).toIntSubmodule

end ReciprocityTheory.GeometryOfNumbersTheory
