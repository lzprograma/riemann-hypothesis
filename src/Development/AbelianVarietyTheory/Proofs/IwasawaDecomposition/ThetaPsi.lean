module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain GlobalTheory.HeightCounting

structure CopyN (D : D7) {D' : D7} (N : TwNew D') (ι : D.what₂.LL →+* D'.what₂.LL) (e : ↥D'.LL0 ≃+* ↥D.LL0) : Prop where
  cp : GlobalTheory.TwInputs.Move.CopyTw D N.toD7 ι e
  jL : HEq D.ntw.jL N.tw.jL
  s2 : HEq D.ntw.s2 N.tw.s2
  lamG : HEq D.ntw.lamG N.tw.lamG
  Xv : HEq D.ntw.Xv N.tw.Xv
  qs : HEq D.ntw.qs N.tw.qs

theorem CopyN.carried {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyN D N ι e) :
    Carried D N.toD7 := by
  refine ⟨h.cp.toSameExport, fun i i' hi x x' hx => ?_⟩
  have hx' : x = e x' := Subtype.ext (D.what₂.embLL.injective
    (hx.trans ((congrArg N.toD7.what₂.embLL (h.cp.LL0 x')).symm.trans (h.cp.embLL _))))
  subst hx'
  exact ⟨h.cp.emb0 i i' hi x', h.cp.emb0b i i' hi x'⟩

end GlobalTheory.HeightCounting.Up

end
