module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.EqZeroOfPMulEqZero
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow

@[expose] public section

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v

section Poly

variable {A : Type u} [CommRing A]

end Poly

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

open tateModule

theorem Acris.logTeich_padicPow (η : tateModule p R) (a : ℤ_[p]) :
    Acris.logTeich (padicPow η a) = algebraMap ℤ_[p] (Acris p R) a * Acris.logTeich η := by
  rw [← sub_eq_zero]
  refine Acris.eq_zero_of_forall_dvd fun k => ?_
  have h := Ideal.mem_span_singleton.1 (PadicInt.appr_spec k a)
  obtain ⟨η', hη'⟩ := exists_padicPow_eq η h
  obtain ⟨b, hb⟩ := h
  refine ⟨Acris.logTeich η' - algebraMap ℤ_[p] (Acris p R) b * Acris.logTeich η, ?_⟩
  have ha : algebraMap ℤ_[p] (Acris p R) a =
      (a.appr k : Acris p R) + (p : Acris p R) ^ k * algebraMap ℤ_[p] (Acris p R) b := by
    conv_lhs => rw [← sub_add_cancel a (a.appr k), hb]
    rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_comm]
  rw [hη', Acris.logTeich_mul, Acris.logTeich_pow, Acris.logTeich_pow, ha, Nat.cast_pow]
  ring


theorem Bcris.algebraMap_padicInt (a : ℤ_[p]) :
    algebraMap ℚ_[p] (Bcris p R) a =
      algebraMap (Acris p R) _ (algebraMap ℤ_[p] (Acris p R) a) :=
  congrArg (algebraMap (BcrisPlus p R) (Bcris p R)) (BcrisPlus.algebraMap_padicInt a)

namespace Bst

open Polynomial

variable [IsDomain R] [CharZero R] [ValuationRing R]

variable [IsAlgClosed (FractionRing R)]




variable (p R) in
def u : Bst p R := logFlat (pflat (p := p) (R := R))

end Bst

end Reformulated.AutPerF
