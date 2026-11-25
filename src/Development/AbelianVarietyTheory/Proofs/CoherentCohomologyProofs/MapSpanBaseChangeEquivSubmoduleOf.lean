module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section

open TensorProduct

namespace GlobalTheory

section General

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable {V V' : Type*} [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']

theorem baseChange_map (f : V →ₗ[R] V') (A : Submodule R V) :
    (A.map f).baseChange S = (A.baseChange S).map (f.baseChange S) := by
  simp only [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image]
  rfl

theorem baseChange_range (f : V →ₗ[R] V') :
    (LinearMap.range f).baseChange S = LinearMap.range (f.baseChange S) := by
  rw [← Submodule.map_top, baseChange_map, Submodule.baseChange_top, Submodule.map_top]

theorem ker_baseChange_mkQ (B : Submodule R V) :
    LinearMap.ker (B.mkQ.baseChange S) = B.baseChange S := by
  rw [Submodule.baseChange, ← LinearMap.exact_iff]
  exact lTensor_exact S (LinearMap.exact_subtype_mkQ B) B.mkQ_surjective

noncomputable def baseChangeQuotEquiv (B : Submodule R V) :
    S ⊗[R] (V ⧸ B) ≃ₗ[S] (S ⊗[R] V) ⧸ B.baseChange S :=
  TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S B

variable [Module.Flat R S]

theorem baseChange_ker (f : V →ₗ[R] V') :
    (LinearMap.ker f).baseChange S = LinearMap.ker (f.baseChange S) := by
  rw [Submodule.baseChange, eq_comm, ← LinearMap.exact_iff]
  exact Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map f)

theorem baseChange_comap (f : V →ₗ[R] V') (B : Submodule R V') :
    (B.comap f).baseChange S = (B.baseChange S).comap (f.baseChange S) := by
  rw [← ker_baseChange_mkQ S B, ← LinearMap.ker_comp, ← LinearMap.baseChange_comp,
    ← baseChange_ker, LinearMap.ker_comp, Submodule.ker_mkQ]

theorem baseChange_inf (A B : Submodule R V) :
    (A ⊓ B).baseChange S = A.baseChange S ⊓ B.baseChange S := by
  rw [← Submodule.map_comap_subtype, baseChange_map, baseChange_comap, Submodule.map_comap_eq]
  rfl

theorem baseChange_iInf {ι : Type*} [Finite ι] (A : ι → Submodule R V) :
    (⨅ i, A i).baseChange S = ⨅ i, (A i).baseChange S := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih => rw [← e.iInf_comp, ← e.iInf_comp, ih]
  | h_empty => rw [iInf_of_empty, iInf_of_empty, Submodule.baseChange_top]
  | h_option ih => rw [iInf_option, iInf_option, baseChange_inf, ih]

theorem baseChange_injective {f : V →ₗ[R] V'} (hf : Function.Injective f) :
    Function.Injective (f.baseChange S) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := S) f hf

noncomputable def baseChangeEquiv (A : Submodule R V) : S ⊗[R] A ≃ₗ[S] A.baseChange S :=
  LinearEquiv.ofInjective (A.subtype.baseChange S) (baseChange_injective S A.injective_subtype)

theorem map_baseChangeEquiv_submoduleOf (A B : Submodule R V) :
    ((B.submoduleOf A).baseChange S).map (baseChangeEquiv S A : S ⊗[R] A →ₗ[S] A.baseChange S) =
      (B.baseChange S).submoduleOf (A.baseChange S) := by
  rw [Submodule.submoduleOf, baseChange_comap, Submodule.map_equiv_eq_comap_symm,
    ← Submodule.comap_comp, Submodule.submoduleOf]
  congr 1
  ext1 x
  obtain ⟨y, rfl⟩ := (baseChangeEquiv S A).surjective x
  change (A.subtype.baseChange S) ((baseChangeEquiv S A).symm ((baseChangeEquiv S A) y)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem lift_rank_baseChange.{u, v, w} {R : Type u} (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] [NoZeroDivisors S] [FaithfulSMul R S]
    {V : Type w} [AddCommGroup V] [Module R V] (A : Submodule R V) :
    Cardinal.lift.{w} (Module.rank S (A.baseChange S)) = Cardinal.lift.{max v w} (Module.rank R A) := by
  rw [← (baseChangeEquiv S A).rank_eq]
  exact (TensorProduct.isBaseChange R A S).lift_rank_eq

theorem finrank_baseChange [NoZeroDivisors S] [FaithfulSMul R S] (A : Submodule R V) :
    Module.finrank S (A.baseChange S) = Module.finrank R A := by
  simpa using! congr_arg Cardinal.toNat (lift_rank_baseChange S A)

end General

section Lattice

variable {R : Type*} (K S L : Type*) [CommRing R] [Field K] [CommRing S] [CommRing L]
  [Algebra R K] [Algebra K L] [Algebra S L]
variable {V V' : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']

def spanBaseChange (M : Submodule R V) : Submodule S (L ⊗[K] V) :=
  Submodule.span S ((fun m => (1 : L) ⊗ₜ[K] m) '' (M : Set V))

variable [Algebra R S] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]


variable (R V) in
noncomputable def baseChangeToField : S ⊗[R] V →ₗ[S] L ⊗[K] V :=
  LinearMap.liftBaseChange S ((TensorProduct.mk K L V 1).restrictScalars R)

@[simp]
theorem baseChangeToField_tmul (s : S) (v : V) :
    baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V) (s ⊗ₜ v) = algebraMap S L s ⊗ₜ[K] v := by
  simp [baseChangeToField, smul_tmul', Algebra.smul_def]

theorem spanBaseChange_eq_map (M : Submodule R V) :
    spanBaseChange K S L M = (M.baseChange S).map (baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V)) := by
  simp only [spanBaseChange, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image, TensorProduct.mk_apply, baseChangeToField_tmul, map_one]

variable [IsFractionRing R K] [FaithfulSMul S L]


variable (R V) in
theorem baseChangeToField_injective : Function.Injective (baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V)) := by
  have hflat : Module.Flat R V :=
    (Module.flat_iff_of_isLocalization K (nonZeroDivisors R) V).1 inferInstance
  have h1 : Function.Injective ((IsScalarTower.toAlgHom R S L).toLinearMap.rTensor V) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective S L)
  have h2 : ∀ x, IsLocalization.moduleTensorEquiv (nonZeroDivisors R) K L V
      (baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V) x) = (IsScalarTower.toAlgHom R S L).toLinearMap.rTensor V x := by
    intro x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul s v => rw [baseChangeToField_tmul]; rfl
  intro x y hxy
  apply h1
  rw [← h2, ← h2, hxy]

variable [Module.Flat R S]

noncomputable def spanBaseChangeEquiv (M : Submodule R V) :
    S ⊗[R] M ≃ₗ[S] spanBaseChange K S L M :=
  baseChangeEquiv S M ≪≫ₗ
    Submodule.equivMapOfInjective _ (baseChangeToField_injective (R := R) (K := K) (S := S) (L := L) (V := V)) _ ≪≫ₗ
    LinearEquiv.ofEq _ _ (spanBaseChange_eq_map K S L M).symm

@[simp]
theorem coe_spanBaseChangeEquiv_apply (M : Submodule R V) (x : S ⊗[R] M) :
    (spanBaseChangeEquiv K S L M x : L ⊗[K] V) =
      baseChangeToField (R := R) (K := K) (S := S) (L := L) (V := V) (M.subtype.baseChange S x) := rfl

theorem map_spanBaseChangeEquiv_submoduleOf (M N : Submodule R V) :
    ((N.submoduleOf M).baseChange S).map
        (spanBaseChangeEquiv K S L M : S ⊗[R] M →ₗ[S] spanBaseChange K S L M) =
      (spanBaseChange K S L N).submoduleOf (spanBaseChange K S L M) := by
  rw [Submodule.submoduleOf, baseChange_comap, Submodule.map_equiv_eq_comap_symm]
  ext x
  obtain ⟨y, rfl⟩ := (spanBaseChangeEquiv K S L M).surjective x
  rw [Submodule.submoduleOf, spanBaseChange_eq_map K S L N]
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    Submodule.subtype_apply, coe_spanBaseChangeEquiv_apply]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨z, hz, h⟩ => baseChangeToField_injective (R := R) (K := K) (S := S) (L := L) (V := V) h ▸ hz⟩

noncomputable def spanBaseChangeSubquotEquiv (M N : Submodule R V) :
    S ⊗[R] (M ⧸ N.submoduleOf M) ≃ₗ[S]
      spanBaseChange K S L M ⧸ (spanBaseChange K S L N).submoduleOf (spanBaseChange K S L M) :=
  baseChangeQuotEquiv S (N.submoduleOf M) ≪≫ₗ
    Submodule.Quotient.equiv _ _ (spanBaseChangeEquiv K S L M)
      (map_spanBaseChangeEquiv_submoduleOf K S L M N)

end Lattice

end GlobalTheory
