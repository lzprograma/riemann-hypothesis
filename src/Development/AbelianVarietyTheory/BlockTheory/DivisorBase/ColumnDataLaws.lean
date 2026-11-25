module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct

section Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

end Theta

section Frame

variable {D : D7}

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

structure DictDat (U : Unf Xo c σ r) where
  g : ℕ
  e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)
  F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)
  ik : U.Comp → Fin F.n
  φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ
  th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

variable {U : Unf Xo c σ r} (W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)

def DictDat.Is (d : DictDat U) : Prop :=
  (∀ k τ, IsInfEmb τ.1 (d.th k τ)) ∧ DictLat U W hr dict ι d.e d.F d.ik d.φ d.th x₀

end Frame

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure RowDat (T : CoreJ D) (G : Type) (i : Fin D.R.m) where

  c' : Coeff T.Q.l
  hle : T.Q.c.F ≤ c'.F

  lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
    ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
  hV : T.V ((i : ℕ) + 1) (c'.F.val.toRingHom.comp (incF T.Q.c c' hle)) = Wc D i

namespace RowDat

variable {T : CoreJ D} {i : Fin D.R.m} (Y : RowDat T G i)

abbrev σ' : Y.c'.F →+* ℂ := Y.c'.F.val.toRingHom

abbrev σ : T.Q.c.F →+* ℂ := Y.σ'.comp (incF T.Q.c Y.c' Y.hle)


abbrev U : Unf (T.Q.Xo ((i : ℕ) + 1)) T.Q.c Y.σ D.R.r := T.U ((i : ℕ) + 1) Y.σ

def dict : GA D (Wc D i) → Σ k, Frame (Y.U.X k).Ψ D.R.r := castDict Y.hV (T.dict ((i : ℕ) + 1) Y.σ)

def ι (_Y : RowDat T G i) : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  have hr : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.succ_pos _) i.2
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)


variable (R : RealDat D A Ks)


end RowDat

end Row

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws
