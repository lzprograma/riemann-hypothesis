module

public import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
public import Formalism.LocalToGlobal.HermitianColumns.TiedQC
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

variable {D : D7}

structure TwAtT (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) where

  eVT : (Tw.A u μ).vT ≃ (D.mem u).A.vT

  eFv : ∀ v, (Tw.A u μ).Fv v ≃+* (D.mem u).A.Fv (eVT v)

def TwAtT.eV {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} (a : TwAtT Tw u μ) (At : AtTTied u) :
    (Tw.A u μ).vT ≃ PlT D u := a.eVT.trans At.eV

def TwAtT.res {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} (a : TwAtT Tw u μ) (At : AtTTied u) (v : (Tw.A u μ).vT) :
    𝓞 D.host.E →+* (Tw.A u μ).Fv v := ((a.eFv v).symm : _ →+* _).comp (At.res (a.eVT v))

variable {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def okQ (D : D7) (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : D.what₂.places.Pl) : Prop :=
  ∀ v ∈ Q, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal

end Formalism.L2.Forms

end
