module

public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Formalism.LocalRingCardinality.SpanPowerMembership.GenericMemberLevelNearLower
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

structure ClsPkg : Type 1 where
  cls : ℕ → Type
  clsFin : ∀ i, Fintype (cls i)
  stab : ∀ i, cls i → Type
  stabGrp : ∀ i c, Group (stab i c)
  stabFin : ∀ i c, Finite (stab i c)
  DGam : ℕ
  DGam_pos : 0 < DGam
  dvd : ∀ i c, Nat.card (stab i c) ∣ DGam

section FormsY

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
  (Pl : Rows.Places LL) {Tau : Type} [Fintype Tau] (hTau : Fintype.card Tau = R.f)
  {hc : Tau → HCParam R} (C : ColumnChain R Tau hc) [hE : ∀ i, IsEmpty (C.Y i)]
  (A : ColumnsAtT R C) (P : PeriodMap R C)

end FormsY

section Member3

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg)

abbrev chain3 : ColumnChain R Tau hc where
  cls := K.cls
  clsFin := K.clsFin
  stab := K.stab
  stabGrp := K.stabGrp
  stabFin := K.stabFin
  DGam := K.DGam
  DGam_pos := K.DGam_pos
  dvd_DGam := fun i _ c => K.dvd i c
  Y := fun _ => Empty
  de := fun _ y => y.elim
  de_ne := fun _ y => y.elim
  rhoDet := fun _ _ => 1
  rhoDet' := fun _ _ => 1
  rho_norm := fun _ _ _ => norm_one
  rho'_norm := fun _ _ _ => norm_one
  unf := fun _ _ _ => 0
  sSharp := fun i τ => if h : i < R.m then (sInt R (hc τ) ⟨i, h⟩).2.choose else 0
  sSharp_eq := fun i h τ => by rw [dite_eq_left h]; exact (sInt R (hc τ) ⟨i, h⟩).2.choose_spec.symm
  sDiv := fun i τ => if h : i < R.m then (sInt R (hc τ) ⟨i, h⟩).1.choose else 0
  sDiv_eq := fun i h τ => by rw [dite_eq_left h]; exact (sInt R (hc τ) ⟨i, h⟩).1.choose_spec.symm

variable (T : ℕ) [hT : Fact T.Prime]

abbrev classLevelColumnsAt (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam) : ColumnsAtT R (chain3 hc K) :=
  haveI : NeZero T := ⟨hT.out.ne_zero⟩
  { T := T
    T_prime := hT.out
    vT := Fin R.f
    card_vT := Fintype.card_fin _
    Fv := fun _ => ZMod T
    card_Fv := fun _ => ZMod.card T
    psiT := fun _ => ZMod.stdAddChar
    psiT_ne := fun _ => by
      have := ZMod.isPrimitive_stdAddChar T (one_ne_zero (α := ZMod T))
      rwa [AddChar.mulShift_one] at this
    rhoT := fun _ => 1
    Mu0 := ⊥
    Mu0_fd := inferInstance
    Mu0_stable := fun _ _ => by simp
    duStar := du
    duStar_pos := hdu
    Dstar := Dst
    Dstar_pos := hD
    GamP := Gam
    one_lt_gammaP := hG }

abbrev period3 : PeriodMap R (chain3 hc K) where
  Mt := Z0
  Wz := PUnit
  evz := 0
  Wrow := PUnit
  lowerMap := 0
  period := 0

abbrev mem3 (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam) : Member R Tau hc :=
  ⟨chain3 hc K, classLevelColumnsAt hc K T Dst hD du hdu Gam hG, period3 hc K⟩

end Member3


end Formalism.BasicNotions.Examples₂
