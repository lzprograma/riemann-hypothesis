module

public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Rows

open Formalism.BasicNotions Formalism.L2.Host

def muFld (n : ℕ) : Fld := IntermediateField.adjoin ℚ {x : Qb | x ^ n = 1}

def valsOf {E : Type} [Field E] [NumberField E] (ι : Qb →+* ℂ) (s : ℝ) (χ : HChar E) : Set Qb :=
  {x | ∃ v, χ.UnrAt v ∧ ι x = χ.valTw s v}

def valsFld (D : D7) (T : HostTied D) (C : CharFrame D) : Fld :=
  IntermediateField.adjoin ℚ
    ((⋃ j, valsOf T.fr.ι 0 (C.mu0 j)) ∪ valsOf T.fr.ι (1 / 2) C.eta ∪
      valsOf T.fr.ι 0 C.del ∪ valsOf T.fr.ι 0 C.del')

def AbelOver (E' L : Fld) : Prop :=
  E' ≤ L ∧ (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ E', σ x = x) → ∀ y ∈ L, σ y ∈ L) ∧
    ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ E', σ x = x) → (∀ x ∈ E', τ x = x) → ∀ y ∈ L, σ (τ y) = τ (σ y)

local instance nfOfFin (L : Fld) [FiniteDimensional ℚ L] : NumberField L := {}

def UnramOverK (d : ℕ) (L : Fld) [FiniteDimensional ℚ L] : Prop :=
  (NumberField.discr L).natAbs = d ^ (Module.finrank ℚ L / 2)

def IsHilbertCF (d : ℕ) (H : Fld) [FiniteDimensional ℚ H] : Prop :=
  AbelOver (Formalism.L2.Host.KQ d) H ∧ UnramOverK d H ∧
    ∀ (H' : Fld) [FiniteDimensional ℚ H'], AbelOver (Formalism.L2.Host.KQ d) H' → UnramOverK d H' → H' ≤ H

structure KsPieces (_D : D7) (_T : HostTied _D) where
  HK : Fld
  rcf : Fld
  M : Fld
  MDel : Fld
  KPs : Fld
  [HK_fin : FiniteDimensional ℚ HK]
  [rcf_fin : FiniteDimensional ℚ rcf]
  [M_fin : FiniteDimensional ℚ M]
  [MDel_fin : FiniteDimensional ℚ MDel]
  [KPs_fin : FiniteDimensional ℚ KPs]

def rootOrders (D : D7) : List ℕ :=
  [Nat.card (G0g D.nd), D.host.g 0 * (D.host.g 0 - 1), D.host.g 1 * (D.host.g 1 - 1), 3 ^ 4, 5 ^ 4]

def KsQ (D : D7) (T : HostTied D) (C : CharFrame D) (P : KsPieces D T) : Fld :=
  T.fr.j.fieldRange ⊔ (⨆ n ∈ rootOrders D, muFld n) ⊔ valsFld D T C ⊔ P.rcf ⊔ P.M ⊔ P.MDel ⊔ P.KPs

def OsQ (K : Fld) : Set Qb := {x | x ∈ K ∧ IsIntegral ℤ x}

end Formalism.L2.Rows
