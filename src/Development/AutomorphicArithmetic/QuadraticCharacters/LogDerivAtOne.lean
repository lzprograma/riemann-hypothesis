module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

@[expose] public section

open ArithmeticFunction

namespace HostParam

structure AbField where
  N : ℕ
  N_pos : 0 < N
  H : Subgroup (ZMod N)ˣ

namespace AbField

variable (E : AbField)

abbrev Gal : Type := (ZMod E.N)ˣ ⧸ E.H

def res : (ZMod E.N)ˣ →* E.Gal := QuotientGroup.mk' E.H

def inertiaUnits (p : ℕ) : Subgroup (ZMod E.N)ˣ :=
  (ZMod.unitsMap (Nat.ordCompl_dvd E.N p)).ker

def inertia (p : ℕ) : Subgroup E.Gal := (E.inertiaUnits p).map E.res

def IsModulus (M : ℕ) : Prop := ∃ h : M ∣ E.N, (ZMod.unitsMap h).ker ≤ E.H

noncomputable def conductor : ℕ := sInf {M : ℕ | E.IsModulus M}

end AbField

end HostParam
