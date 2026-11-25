module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosCompatOfBase

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.FrobeniusOrbits

namespace Formalism.L2.G

theorem cc_sq (e : Formalism.HC.Frame) : e.cc * e.cc = 1 := by
  simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, Prod.ext_iff]

theorem cc_pow (e : Formalism.HC.Frame) (s : ℕ) : e.cc ^ s = if s % 2 = 1 then e.cc else 1 := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [ite_eq_right (by omega), one_mul, ite_eq_left (by omega)]
    · rw [ite_eq_left h, cc_sq, ite_eq_right (by omega)]

theorem embLL_mem_alg (D : D7) (z : D.what₂.LL) : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic z).algHom D.what₂.embLL.toRatAlgHom

theorem emb_conj_pow (D : D7) (g : D.R.GG) (s : ℕ) (x : D.host.E) :
    D.host.emb (g * D.R.cc ^ s) x = D.host.emb g (if s % 2 = 1 then D.host.conj x else x) := by
  rw [emb_mul, cc_pow]
  split_ifs
  · rfl
  · simp [Formalism.BasicNotions.Host.sigmaOf]

end Formalism.L2.G
