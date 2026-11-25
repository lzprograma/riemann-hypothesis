module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

variable {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)



theorem isoPair_toTerm (s : TT Y u u') : (eTT Z Y u u' s).toTerm = eRT Z Y u u' s.toTerm := by
  rfl'



theorem isoPair_toTerm_symm (s : TT (reY Z Y) (wd Z u) (wd Z u')) :
    ((eTT Z Y u u').symm s).toTerm = (eRT Z Y u u').symm s.toTerm := by
  rfl'



theorem isoPair_row (a b : TT Y u u') :
    rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) (eTT Z Y u u' a) =
        rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) (eTT Z Y u u' b) ↔
      rowOf Y.TR (Y.cs u) (Y.cs u') a = rowOf Y.TR (Y.cs u) (Y.cs u') b := by
  apply Iff.of_eq
  rfl'



theorem isoPair_row_symm (a b : TT (reY Z Y) (wd Z u) (wd Z u')) :
    rowOf Y.TR (Y.cs u) (Y.cs u') ((eTT Z Y u u').symm a) = rowOf Y.TR (Y.cs u) (Y.cs u') ((eTT Z Y u u').symm b) ↔
      rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) a =
        rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) b := by
  have := isoPair_row Z Y u u' ((eTT Z Y u u').symm a) ((eTT Z Y u u').symm b)
  simpa only [Equiv.apply_symm_apply] using this.symm



theorem isoPair_s0T (a b : TT Y u u') : s0T (eTT Z Y u u' a) (eTT Z Y u u' b) = s0T a b := by
  rfl'



theorem isoPair_lift (a b : TT Y u u') : liftScalar (eTT Z Y u u' a) (eTT Z Y u u' b) ↔ liftScalar a b := by
  apply Iff.of_eq
  rfl'

def isoPairFib (t : RT Y u u') : fib Y t ≃ fib (reY Z Y) (eRT Z Y u u' t) where
  toFun s := ⟨eTT Z Y u u' s.1, by rw [isoPair_toTerm, s.2]⟩
  invFun s := ⟨(eTT Z Y u u').symm s.1, by rw [isoPair_toTerm_symm, s.2, Equiv.symm_apply_apply]⟩
  left_inv s := Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv s := Subtype.ext (Equiv.apply_symm_apply _ _)

def isoPairE : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u') where
  toFun q := ⟨(eRT Z Y u u' q.1.1, eRT Z Y u u' q.1.2), by
    obtain ⟨s₁, s₂, hs⟩ := q.2
    exact ⟨isoPairFib Z Y u u' _ s₁, isoPairFib Z Y u u' _ s₂, (isoPair_row Z Y u u' _ _).2 hs⟩⟩
  invFun q := ⟨((eRT Z Y u u').symm q.1.1, (eRT Z Y u u').symm q.1.2), by
    obtain ⟨s₁, s₂, hs⟩ := q.2
    refine ⟨⟨(eTT Z Y u u').symm s₁.1, by rw [isoPair_toTerm_symm, s₁.2]⟩,
      ⟨(eTT Z Y u u').symm s₂.1, by rw [isoPair_toTerm_symm, s₂.2]⟩, (isoPair_row_symm Z Y u u' _ _).2 hs⟩⟩
  left_inv q := Subtype.ext (by simp)
  right_inv q := Subtype.ext (by simp)



private theorem isoPair_summand (a b : TT Y u u') :
    (if rowOf Y.TR (Y.cs u) (Y.cs u') a = rowOf Y.TR (Y.cs u) (Y.cs u') b then
      inner ℂ (vT Y u u' b) (vT Y u u' a) else 0) =
    (if rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) (eTT Z Y u u' a) =
        rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) (eTT Z Y u u' b) then
      inner ℂ (vT (reY Z Y) (wd Z u) (wd Z u') (eTT Z Y u u' b))
        (vT (reY Z Y) (wd Z u) (wd Z u') (eTT Z Y u u' a)) else 0) := by
  refine ite_congr (propext (isoPair_row Z Y u u' a b).symm) (fun _ => ?_) (fun _ => rfl)
  -- The kernel checks reflexivity for the inner product without repeating the conversion in elaboration.
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun goal => goal.refl (check := false)

theorem rp_iso_pair : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y))
    (u u' : D.what₂.Word), ∃ e : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u'), ∀ q, eRT Z Y u u' q.1.1 = (e q).1.1 ∧
      eRT Z Y u u' q.1.2 = (e q).1.2 ∧ s0T q.l1 q.l2 = s0T (e q).l1 (e q).l2 ∧
      (liftScalar q.l1 q.l2 ↔ liftScalar (e q).l1 (e q).l2) ∧
      pvR h u u' q = pvR h' (wd Z u) (wd Z u') (e q) := by
  intro D Z X Y h h' u u'
  refine ⟨isoPairE Z Y u u', fun q => ⟨rfl, rfl, ?_⟩⟩
  let q' := isoPairE Z Y u u' q
  let a := eTT Z Y u u' q.l1
  let b := eTT Z Y u u' q.l2
  have ha : a.toTerm = q'.l1.toTerm :=
    (isoPair_toTerm Z Y u u' q.l1).trans
      ((congrArg (eRT Z Y u u') q.2.choose.2).trans q'.2.choose.2.symm)
  have hb : b.toTerm = q'.l2.toTerm :=
    (isoPair_toTerm Z Y u u' q.l2).trans
      ((congrArg (eRT Z Y u u') q.2.choose_spec.choose.2).trans q'.2.choose_spec.choose.2.symm)
  obtain ⟨hs, hl⟩ := h'.pairIndep (wd Z u) (wd Z u') a b q'.l1 q'.l2 ha hb
    ((isoPair_row Z Y u u' q.l1 q.l2).2 q.2.choose_spec.choose_spec) q'.2.choose_spec.choose_spec
  refine ⟨(isoPair_s0T Z Y u u' q.l1 q.l2).symm.trans hs,
    (isoPair_lift Z Y u u' q.l1 q.l2).symm.trans hl, ?_⟩
  unfold pvR
  exact @Fintype.sum_equiv _ _ ℂ
    (@instFintypeProd _ _ (h.fibFT q.1.1) (h.fibFT q.1.2))
    (@instFintypeProd _ _ (h'.fibFT q'.1.1) (h'.fibFT q'.1.2)) _
    ((isoPairFib Z Y u u' q.1.1).prodCongr (isoPairFib Z Y u u' q.1.2)) _ _
    (fun r => isoPair_summand Z Y u u' r.1.1 r.2.1)

end GlobalTheory.Mem.SRe
