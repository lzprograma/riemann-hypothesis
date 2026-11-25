module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def reFaceErr (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) : type_of% R.err0 :=
  fun w _ => errOf ((R.toCx3 F).data (reFace F Dc Sp Zsc).cr false) ((reFace F Dc Sp Zsc).fc (R.toCx3 F).zs).Z.F0 w



private theorem toCx3_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    R.toCx3 (reFace F Dc Sp Zsc) = R.toCx3 F := by
  dsimp only [RealDat3.toCx3, reFace, Face3.lv2]
  rfl

private theorem toCx3_withErr (R : RealDat3 D A3 Ks) (F : Face3 D A3) (e : type_of% R.err0) :
    (R.withErr e).toCx3 F = reErr (R.toCx3 F) e := by
  dsimp only [RealDat3.toCx3, RealDat3.withErr, reErr]
  rfl

private theorem errOf_data_reErr {K : Type} [Field K] [NumberField K] [StarRing K]
    {Bs : DefBase K} {Am : DefAmb Bs} (X : CxData Am) (e : type_of% X.err0)
    {fc : DefSub Am → DefFace Bs} (cr : Crd Am fc) (w : HeightOneSpectrum (𝓞 K)) :
    errOf ((reErr X e).data cr false) (fc (reErr X e).zs).Z.F0 w =
      errOf (X.data cr false) (fc X.zs).Z.F0 w := by
  dsimp only [errOf, IndefData.Iw, CxData.data, CxData.liftMat, CxData.liftMatC, CxData.tC,
    CxData.w0C, CxData.wC, CxData.zs, CxData.Z, CxData.Zl, reErr]
  rfl


theorem reFace_errEq (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    ErrEq (R.withErr (reFaceErr R F Dc Sp Zsc)) (reFace F Dc Sp Zsc) := by
  intro w j
  let F' := reFace F Dc Sp Zsc
  let e := reFaceErr R F Dc Sp Zsc
  change e w j = errOf (((R.withErr e).toCx3 F').data F'.cr false)
    (F'.fc ((R.withErr e).toCx3 F').zs).Z.F0 w
  rw [toCx3_withErr, toCx3_reFace, errOf_data_reErr]
  rfl



theorem reFace_keep (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : Keep (A3 := A3) R.toRealDat F.lv2 cG) :
    Keep (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 cG :=
  ⟨h.std, h.signs, h.frames, h.beta, h.prX, h.grp, h.psi, h.guard, h.valKs, h.frameKs, h.levKs⟩



theorem reFace_keep_back (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0)
    (h : Keep (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 cG) : Keep (A3 := A3) R.toRealDat F.lv2 cG :=
  ⟨h.std, h.signs, h.frames, h.beta, h.prX, h.grp, h.psi, h.guard, h.valKs, h.frameKs, h.levKs⟩



theorem reFace_scal (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hl6 : ∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨
      ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v))
    (hs : R.IsScal F) : R.IsScal (reFace F Dc Sp Zsc) := by
  refine ⟨hs.lam0, hs.kap, hs.off, fun i t p hp => ?_, fun i p v hv hp => ?_, hs.tup⟩
  · refine (hs.abs0 i t p hp).trans ?_
    rcases hl6 i with h | h
    · exact congrArg Real.exp h.symm
    · exact absurd hp (h.1 p)
  · refine (hs.abs i p v hv hp).trans ?_
    rcases hl6 i with h | h
    · exact congrArg Real.exp h.symm
    · exact absurd (h.2 p v hv) hp



theorem reFace_pins (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0)
    (hl6 : ∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨
      ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v))
    (hP : Pins R F cG) : Pins (R.withErr e) (reFace F Dc Sp Zsc) cG := by
  have h := RealDat3.weak_characterisation_with_error hP.char e
  have hl6' : ∀ i, (Zsc ((R.withErr e).toCx3 F).zs).l6m i = (F.Zsc ((R.withErr e).toCx3 F).zs).l6m i ∨
      ((∀ p, (R.withErr e).Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → (R.withErr e).PartAt F i p v) := fun i => by
    rw [RealDat3.zs_withErr]
    exact (hl6 i).imp id fun h => ⟨h.1, fun p v hv => (RealDat3.partAt_withErr e i p v).2 (h.2 p v hv)⟩
  exact ⟨⟨h.base, h.inert, h.fullY, h.fullX, h.fullP, reFace_scal (R.withErr e) F Dc Sp Zsc hl6' h.scal, h.tup, h.phase, h.allPl⟩,
    reFace_keep R F cG Dc Sp Zsc e hP.keep, hP.phs, hP.trSem⟩



theorem further_face_statements_independent_of_error (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : UnusedChoiceStatements R F) :
    UnusedChoiceStatements (R.withErr e) (reFace F Dc Sp Zsc) :=
  ⟨⟨h.ex.ItY, h.ex.ItX, h.ex.ioY, h.ex.ioX, h.ex.Th, h.ex.ioP, h.ex.thF, h.ex.thG⟩, h.conj, h.levelW, h.integral⟩



def reFaceRead (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) : Read (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 X0 :=
  { Y with
    mj := ⟨Y.mj.eW, Y.mj.eW_range, Y.mj.eW_norm, Y.mj.eW_lat⟩
    cen0 := fun cG hK => Y.cen0 cG (reFace_keep_back R F cG Dc Sp Zsc e hK)
    cen1 := fun cG hK => Y.cen1 cG (reFace_keep_back R F cG Dc Sp Zsc e hK) }



def reFaceReadL (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ReadL (R.withErr e) (reFace F Dc Sp Zsc) X0 (reFaceRead R F Dc Sp Zsc e X0 Y) :=
  { Z with }

end GlobalTheory.Mem.R3

end
