module

public import Formalism.LocalToGlobal.HermitianForms.TiedTwSym
public import Formalism.LocalToGlobal.HermitianForms.TiedTwP
public import Formalism.LocalToGlobal.HermitianForms.TiedTwPGen

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}



structure SymmetricTwistedTiltedData {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F}
    (_Lv : SymmetricTwistedLevelData W) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m)
    (_K : ClassesAtPrimes (Tw.fm u μ) (badQ D (T.Q μ))) where
  z0 : Fin (D.R.N D.R.m) → D.host.E
  ga : (Tw.fm u μ).clsP → UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
  ka : ∀ c, (W.ch u μ hμ D.R.m h1 le_rfl (T.chOf u μ D.R.m ((Tw.fm u μ).til c))).lev.U



structure TwPTiedS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F} (Lv : SymmetricTwistedLevelData W) where

  cls : ∀ u μ, μ ≠ D.what₂.mu0 → ClassesAtPrimes (Tw.fm u μ) (badQ D (T.Q μ))

  Lb : ∀ u μ hμ, (cls u μ hμ).lev.Lb = (F u).clsP.lev.Lb

  chi_fin : ∀ u μ hμ, ∃ n : ℕ, 0 < n ∧ ∀ κ, (cls u μ hμ).lev.chi κ ^ n = 1

  val : ∀ u μ hμ, ValuationAtPrimes (cls u μ hμ) (okPT D (T.Q μ) (D.mem u).A.T)

  norm : ∀ u μ hμ, NormPTieG (val u μ hμ)

  til : ∀ u μ hμ (h1 : 1 ≤ D.R.m), SymmetricTwistedTiltedData Lv u μ hμ h1 (cls u μ hμ)

structure TwPAtGS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv) : Prop where
  Uloc_g : ∀ u μ hμ v, v ∈ badG D → (P.cls u μ hμ).lev.Uloc v = (F u).clsP.lev.Uloc v
  chi_g : ∀ u μ hμ (κ : (P.cls u μ hμ).lev.U) (κ' : (F u).clsP.lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) → (P.cls u μ hμ).lev.chi κ = (F u).clsP.lev.chi κ'



structure TwPEvzS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv) where
  eWz : ∀ u μ, (D.PTw u μ).Wz ≃ₗ[ℂ] ((Tw.fm u μ).clsP → (D.chTw u μ).Y D.R.m → ℂ)
  evz : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m) (φ : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ) c s s',
    IsTr (atInf (embT D) ((P.til u μ hμ h1).ga c).1.1) (twYS T F u μ D.R.m le_rfl s') (twYS T F u μ D.R.m le_rfl s) →
    eWz u μ ((D.PTw u μ).evz φ) c s =
      ((((W.ch u μ hμ D.R.m h1 le_rfl (T.chOf u μ D.R.m ((Tw.fm u μ).til c))).lev.chi ((P.til u μ hμ h1).ka c))⁻¹ : ℂˣ) : ℂ) *
        φ ((Tw.fm u μ).til c) s'
  jM : ∀ u μ, (D.PTw u μ).Mt →ₛₗ[starRingEnd ℂ] (D.PTw u μ).Wrow
  per : ∀ u μ, μ ≠ D.what₂.mu0 →
    (∀ z ∈ (Tw.fm u μ).ptC, ∃ G, jM u μ G = z) ∧ (∀ G, jM u μ G ∈ (Tw.fm u μ).ptC) ∧
      ∀ w G, (D.PTw u μ).period w G = (Tw.fm u μ).ipP (jM u μ G) w

end Formalism.L2.Forms

end
