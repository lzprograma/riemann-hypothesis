module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum Formalism.IndefR.Lev
open scoped TensorProduct ComplexOrder
open Classical

namespace Formalism.IndefR.NX

variable {D : D7}

structure ExpSet (D : D7) where

  ψ : AddChar (AF D.host.F) ℂ

  θ : InfFam D

  V : HSp D

  W : HSp D

  sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ

  BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ
  pV : D.what₂.Tau → ℕ
  pW : D.what₂.Tau → ℕ

  ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)

  βV : GL (Fin V.rank) (Formalism.IndefR.Datum.EAf D)
  βW : GL (Fin W.rank) (Formalism.IndefR.Datum.EAf D)

  χV : (AE D)ˣ →* Circle
  χW : (AE D)ˣ →* Circle

  om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)

  f₀ : WO V W → ℂ

  gp : Fin 2 → ℕ
  pb : Fin 2 → 𝓞 D.host.E

  Pg : Finset (Formalism.L2.DIV.Pl D.host.E)

  Pd : Finset (Formalism.L2.DIV.Pl D.host.E)

  l : ℕ
  Pl : Finset (Formalism.L2.DIV.Pl D.host.E)

  pde : Fin 2 → ℕ

  e0 : AE D

  Φ0 : WO V W → ℂ

  φ0 : WO V W → ℂ

  ψg : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ

  fr : Formalism.IndefR.Lev.Frm
  posV : ∀ τ, (gramAt D V τ).PosDef
  cartV : ∀ τ, IsCartanInv (gramAt D V τ) (sV τ)
  cartW : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ)
  onbV : ∀ τ, IsONBasis (gramAt D V τ) (sV τ) (BV τ) (pV τ)
  onbW : ∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) (pW τ)
  frV : Formalism.L2.DIV.IsFrame βV ΛV
  frW : Formalism.L2.DIV.IsFrame βW ΛW
  sdV : IsSelfDualC V ΛV
  sdW : IsSelfDualC W ΛW
  weil : IsWeilDatumO ψ V W χV χW om
  vac : IsVacO ψ θ V W sV sW ΛV ΛW f₀
  typePl : IsTypePlaces (D := D) gp pb Pg
  genPsi : Formalism.L2.DIV.IsGenericPsi Pg ψg
  lPl : ∀ PP : Formalism.L2.DIV.Pl D.host.E, PP ∈ Pl ↔ ((l : 𝓞 D.host.E) ∈ PP.asIdeal)
  idempotent_sum : IsIdemSum e0 (Pg ∪ Pd)
  φ0_vec : IsThetaAt ψ (symplO V W) (heisO ψ V W) (cA D e0) (latO V W ΛV ΛW fun _ => True) 1 f₀ Φ0 φ0

namespace ExpSet

variable (S : ExpSet D)

def KV : Subgroup (GA D S.V) := levA S.V (Formalism.L2.DIV.Kg D.sp.cm S.V.gram S.βV ∅)

end ExpSet

theorem isConjPl_conjPl (PP : Formalism.L2.DIV.Pl D.host.E) : IsConjPl (D := D) PP (Formalism.L2.DIV.conjPl PP) :=
  fun c hc => ⟨Formalism.L2.DIV.starO c,
    (Formalism.L2.DIV.isConjPl_conjPl PP c (Formalism.L2.DIV.starO c) (Formalism.L2.DIV.starO_coe c)).1 hc, Formalism.L2.DIV.starO_coe c⟩

structure CoefLat (S : ExpSet D) (O : Type) [CommRing O] where
  ι : O →+* ℂ
  Cf : Type
  [acg : AddCommGroup Cf]
  [md : Module O Cf]
  LL : GA D S.V → Submodule O Cf
  act : GA D S.V → (Cf ≃ₗ[O] Cf)
  rd : Cf →+ MvPolynomial (FVar D S.W.rank S.V.rank) ℂ
  rd_smul : ∀ (a : O) (x : Cf), rd (a • x) = MvPolynomial.C (ι a) * rd x
  LL_left : ∀ γ ∈ GQ S.V, ∀ h, (LL h).map (act γ).toLinearMap = LL (γ * h)
  LL_right : ∀ h, ∀ k ∈ S.KV, LL (h * k) = LL h

attribute [instance] CoefLat.acg CoefLat.md

section SuppHalf

variable {m n : ℕ}

end SuppHalf

variable {S : ExpSet D} {O : Type} [CommRing O] {C : CoefLat S O}

end Formalism.IndefR.NX
