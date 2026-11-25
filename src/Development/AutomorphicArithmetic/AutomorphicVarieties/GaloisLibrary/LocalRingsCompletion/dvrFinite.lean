module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton
public import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PowerSeries.Basic
public import Formalism.SharedLemmas.PrecompleteFinite

@[expose] public section

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem prec_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] :
    IsPrecomplete I M := by
  first
  | exact _root_.Formalism.SharedLemmas.isPrecomplete_of_moduleFinite
  | (apply _root_.Formalism.SharedLemmas.isPrecomplete_of_moduleFinite <;> assumption)

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

theorem UpperTheory.V.abelian₂.dvr_finite :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      IsAdicComplete (maximalIdeal O) O ∧ Finite (ResidueField O) ∧ (l : O) ∈ maximalIdeal O ∧
        Function.Injective (algebraMap ℤ_[l] O) ∧ Module.Free ℤ_[l] O ∧ IsLocalHom (algebraMap ℤ_[l] O) := by
  intro l hl O _ _ _ _ _ _
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hinj : Function.Injective (algebraMap ℤ_[l] O) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    exact mul_ne_zero ((PadicInt.unitCoeff h0).isUnit.map _).ne_zero (pow_ne_zero _ hl0) hx
  have : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hfree : Module.Free ℤ_[l] O := Module.free_of_finite_type_torsion_free'
  have hloc : IsLocalHom (algebraMap ℤ_[l] O) := inferInstance
  have hlm : (l : O) ∈ maximalIdeal O := by
    have h : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    have := map_nonunit (algebraMap ℤ_[l] O) _ h
    rwa [map_natCast] at this
  have hres : Finite (ResidueField O) := by
    have : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  refine ⟨?_, hres, hlm, hinj, hfree, hloc⟩
  have hP : IsPrecomplete (maximalIdeal O) O := by
    have h1 : IsPrecomplete ((maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) O :=
      IsPrecomplete.map_algebraMap_iff.2 (prec_free _)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast] at h1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := Ideal.span {(l : O)}) (by simpa using hl0) hϖ
    refine prec_cofinal ((Ideal.span_singleton_le_iff_mem _).2 hlm) (e := e) ?_ h1
    rw [he, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
