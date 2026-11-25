module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped TensorProduct NumberField
open Polynomial

namespace GlobalTheory

namespace EigenSplit

section Saturation

variable {O : Type*} [CommRing O] {R : Type*} [CommRing R]
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']

theorem eigenSub_eq_iInf_ker (ρ : O →+* Module.End R N) (χ : O →+* R) {s : Set O}
    (hs : Submodule.span ℤ s = ⊤) :
    eigenSub ρ χ = ⨅ a : s, LinearMap.ker (ρ a - χ a • LinearMap.id) := by
  ext x
  simp only [mem_eigenSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine ⟨fun h a => h a, fun h a => ?_⟩
  have ha : a ∈ Submodule.span ℤ s := hs ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem a ha => exact h ⟨a, ha⟩
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb, add_smul]
  | smul n a _ ha => rw [map_zsmul, map_zsmul, LinearMap.smul_apply, ha, smul_assoc]

theorem IsEquivariant.symm {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {e : N ≃ₗ[R] N'} (he : IsEquivariant ρ ρ' (e : N →ₗ[R] N')) :
    IsEquivariant ρ' ρ (e.symm : N' →ₗ[R] N) := fun a y => by
  obtain ⟨x, rfl⟩ := e.surjective y
  have := he a x
  simp only [LinearEquiv.coe_coe] at this ⊢
  rw [← this, e.symm_apply_apply, e.symm_apply_apply]

theorem IsEquivariant.map_eigenSub {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {e : N ≃ₗ[R] N'} (he : IsEquivariant ρ ρ' (e : N →ₗ[R] N')) (χ : O →+* R) :
    (eigenSub ρ χ).map (e : N →ₗ[R] N') = eigenSub ρ' χ := by
  refine le_antisymm ?_ fun y hy => ⟨e.symm y, he.symm.map_mem hy, e.apply_symm_apply y⟩
  rintro _ ⟨x, hx, rfl⟩
  exact he.map_mem hx

end Saturation

section FlatBaseChange

variable {O : Type*} [CommRing O] {R : Type*} [CommRing R]
  {N : Type*} [AddCommGroup N] [Module R N] {R' : Type*} [CommRing R'] [Algebra R R']
  {M : Type*} [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
  {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R' M} {f : N →ₗ[R] M}

theorem isEquivariant_equiv (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange R' f) :
    IsEquivariant (baseChangeAction R' ρ) ρ' (hb.equiv : R' ⊗[R] N →ₗ[R'] M) := by
  intro a t
  induction t using TensorProduct.inductionOn with
  | tmul r x =>
    change hb.equiv (r ⊗ₜ[R] ρ a x) = ρ' a (hb.equiv (r ⊗ₜ[R] x))
    simp [hf]
  | add s t hs ht => simp only [map_add (f := _), hs, ht]

variable [Module.Finite ℤ O] [Module.Flat R R']


variable (R' ρ) in
theorem eigenSub_baseChangeAction_of_flat (χ : O →+* R) :
    eigenSub (baseChangeAction R' ρ) ((algebraMap R R').comp χ)
      = (eigenSub ρ χ).baseChange R' := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := O)
  rw [eigenSub_eq_iInf_ker _ _ hs, eigenSub_eq_iInf_ker _ _ hs, baseChange_iInf]
  refine iInf_congr fun a => ?_
  rw [baseChange_ker]
  congr 1
  ext x
  simp
  rfl

theorem eigenSub_eq_span_of_flat (hf : ∀ a x, f (ρ a x) = ρ' a (f x))
    (hb : IsBaseChange R' f) (χ : O →+* R) :
    eigenSub ρ' ((algebraMap R R').comp χ) = Submodule.span R' (f '' eigenSub ρ χ) := by
  rw [← (isEquivariant_equiv hf hb).map_eigenSub, eigenSub_baseChangeAction_of_flat,
    Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
  simp

end FlatBaseChange

section Tower

variable (A : Type*) [CommRing A] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
  [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
  (N : Type*) [AddCommGroup N] [Module A N]


end Tower

section Determinant

variable {O : Type*} [CommRing O] [Module.Finite ℤ O] {A : Type*} [CommRing A] [IsDomain A]
  {ι : Type*} [Fintype ι] {σ : ι → O →+* A}
  {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] {ρ : O →+* Module.End A N}



variable (h : IsSplitting fun i => (algebraMap A (FractionRing A)).comp (σ i))
include h


variable [Module.Flat A N] {S : Type*} [CommRing S] [Algebra A S]
  {M : Type*} [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
  {ρ' : O →+* Module.End S M} {f : N →ₗ[A] M}

end Determinant

section Factor

variable {O : Type*} [CommRing O] [Module.Finite ℤ O] {A : Type*} [CommRing A]
  {ι : Type*} [Finite ι] {σ : ι → O →+* A}
  {N : Type*} [AddCommGroup N] [Module A N] {ρ : O →+* Module.End A N}
  {S : Type*} [CommRing S] [Algebra A S]
  {M : Type*} [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
  {ρ' : O →+* Module.End S M} {f : N →ₗ[A] M}

omit [Module.Finite ℤ O] in
private theorem eigenSub_eq_span_of_isBaseChange {hf : ∀ a x, f (ρ a x) = ρ' a (f x)}
    {χ : O →+* A} (hb : IsBaseChange S (eigenMapAlgebra hf χ)) :
    eigenSub ρ' ((algebraMap A S).comp χ) = Submodule.span S (f '' eigenSub ρ χ) := by
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · change ((⟨y, hy⟩ : eigenSub ρ' ((algebraMap A S).comp χ)) : M) ∈ _
    refine hb.inductionOn ⟨y, hy⟩
      (motive := fun z => (z : M) ∈ Submodule.span S (f '' eigenSub ρ χ))
      (fun x => Submodule.subset_span ⟨x, x.2, rfl⟩) (fun s _ hz => Submodule.smul_mem _ s hz)
      fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂
  · rintro _ ⟨x, hx, rfl⟩
    exact map_mem_eigenSub_algebraMap hf hx

theorem eigenSub_eq_span_of_factor (B : Type*) [CommRing B] [Algebra A B] [Module.Flat A B]
    [Algebra B S] [IsScalarTower A B S] (hB : IsSplitting fun i => (algebraMap A B).comp (σ i))
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange S f) (i : ι) :
    eigenSub ρ' ((algebraMap A S).comp (σ i)) = Submodule.span S (f '' eigenSub ρ (σ i)) := by
  let : Module B M := Module.compHom M (algebraMap B S)
  have : IsScalarTower B S M := ⟨fun x y z => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : IsScalarTower A B M := IsScalarTower.to₁₂₄ _ _ S _
  have hN := TensorProduct.isBaseChange A N B
  have hb' : IsBaseChange S (hN.lift f) := hN.of_comp (by rwa [hN.lift_comp])
  have hf' : ∀ a x, hN.lift f (baseChangeAction B ρ a x) = ρ' a (hN.lift f x) := by
    intro a x
    induction x using hN.inductionOn with
    | tmul x => rw [← mk_equivariant, hN.lift_eq, hN.lift_eq, hf]
    | smul s x hx =>
      rw [map_smul, map_smul, map_smul, hx, ← algebraMap_smul S s, ← algebraMap_smul S s, map_smul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 := eigenSub_eq_span_of_isBaseChange (isBaseChange_eigenMapAlgebra hB hf' hb' i)
  rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq,
    eigenSub_eq_span_of_flat (mk_equivariant B ρ) hN, ← Submodule.map_coe, Submodule.map_span,
    Submodule.span_span_of_tower, Set.image_image] at h1
  simpa only [hN.lift_eq] using h1

end Factor

section Valuation

variable {O : Type*} [CommRing O] {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
  {M : Type*} [AddCommGroup M] [Module V M]


variable [Module.Finite V M] [Module.IsTorsionFree V M] (ρ : O →+* Module.End V M) (χ : O →+* V)

end Valuation

section Frames

variable {R : Type*} [CommRing R] {K : Type*} [CommRing K] [Algebra R K]
  {P : Type*} [AddCommGroup P] [Module R P]
  {W : Type*} [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]
  {ι : Type*} [Fintype ι] (b b' : Module.Basis ι R P) (j : P →ₗ[R] W)

variable [LinearOrder ι]


variable {O : Type*} [CommRing O] {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] {ρ : O →+* Module.End R M} {ρ' : O →+* Module.End R M'}

end Frames

section Integers

variable {E : Type*} [Field E] [NumberField E] {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
  {ι : Type*} [Fintype ι] {σ : ι → 𝓞 E →+* A}


omit [CharZero A] in
theorem flat_int_iff_charZero : Module.Flat ℤ A ↔ CharZero A := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot, Module.isTorsionFree_iff_algebraMap_injective]
  exact ⟨fun h => charZero_of_injective_algebraMap h, fun _ => RingHom.injective_int _⟩

omit [IsDomain A] [CharZero A] in
theorem isUnit_discr_of_charZero (K : Type*) [Field K] [CharZero K] :
    IsUnit (NumberField.discr E : K) := by
  simpa using NumberField.discr_ne_zero E

variable (hσ : Function.Injective σ) (hc : Fintype.card ι = Module.finrank ℚ E)
include hσ hc

variable {N : Type*} [AddCommGroup N] [Module A N] {ρ : 𝓞 E →+* Module.End A N}
  {S : Type*} [CommRing S] [Algebra A S]
  {M : Type*} [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
  {ρ' : 𝓞 E →+* Module.End S M} {f : N →ₗ[A] M}

variable [Module.Finite A N] [Module.Flat A N]

end Integers

end EigenSplit

universe u v



end GlobalTheory
