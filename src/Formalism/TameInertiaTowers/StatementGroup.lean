module

public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.PGroup
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace Formalism.TwoAdicCyclotomicDecomposition

abbrev GalL (n : ℕ) : Type := (ZMod (2 ^ n))ˣ × ℤˣ × ℤˣ

def JJ (n : ℕ) : GalL n := (-1, -1, -1)

def D2 (n : ℕ) : Subgroup (GalL n) :=
  ((MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.snd (ZMod (2 ^ n))ˣ (ℤˣ × ℤˣ))).ker

def I2 (n : ℕ) : Subgroup (GalL n) := (MonoidHom.snd (ZMod (2 ^ n))ˣ (ℤˣ × ℤˣ)).ker

def Iq (n : ℕ) : Subgroup (GalL n) := Subgroup.zpowers ((1, -1, 1) : GalL n)

def Id (n : ℕ) : Subgroup (GalL n) := Subgroup.zpowers ((1, 1, -1) : GalL n)

def u5 (n : ℕ) : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right n (by norm_num))

def u3 (n : ℕ) : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 3 (Nat.Coprime.pow_right n (by norm_num))

def resMap {s m : ℕ} (h : s ≤ m) : GalL (m + 2) →* GalL (s + 2) :=
  MonoidHom.prodMap (ZMod.unitsMap (pow_dvd_pow 2 (by omega))) (MonoidHom.id (ℤˣ × ℤˣ))

abbrev GamE (s : ℕ) : Type := GalL (s + 2) ⧸ Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2))

def GG {s m : ℕ} (h : s ≤ m) : Subgroup (GalL (m + 2)) :=
  ((QuotientGroup.mk' (Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)))).comp (resMap h)).ker

def RankBound : Prop :=
  ∀ r : ℕ, 1 ≤ r → (r * (r - 1) / 2 ≤ 3 + (r - 1) ↔ r ≤ 4)

def TwistVal : Prop :=
  ∀ s e : ℕ, 0 < e → padicValInt 2 ((5 : ℤ) ^ (2 ^ s * e) - 1) = s + 2 + padicValNat 2 e

end Formalism.TwoAdicCyclotomicDecomposition
