module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open scoped ENNReal Matrix

section BK

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

def IsCrysCocycle (T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀) (f : ↥Gw → Fin m → O₀) : Prop :=
  (fun (g : ↥(Loc.GK Bw.Kw)) (j : Fin m) => Bw.toLL (f (Bw.e.symm g) j)) ∈
    Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))

variable {O' : Type} [CommRing O'] [IsDomain O'] (ι : O₀ →+* O')

end BK

def IsWildAt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (σ : G E Ω) : Prop :=
  ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1

section HidaSetting

variable (D : D7) (i : D.ntw.Tw)

abbrev GE : Type := G D.host.E D.nd.Om

abbrev decAt (v : PlE D.host) : Subgroup (GE D) := Dec (F := D.host.E) (D.nd.plOm.1 v)

end HidaSetting

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles
