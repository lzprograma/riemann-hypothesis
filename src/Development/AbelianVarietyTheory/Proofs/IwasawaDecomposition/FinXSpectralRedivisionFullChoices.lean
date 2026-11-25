module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe



theorem toTerm_eTT_symm {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (s : TT (reY Z Y) (wd Z u) (wd Z u')) :
    ((eTT Z Y u u').symm s).toTerm = (eRT Z Y u u').symm s.toTerm := by
  have termRefl := Eq.refl ((eRT Z Y u u').symm s.toTerm)
  run_tac
    -- The kernel checks the conversion after the equivalences reduce.
    Lean.Elab.Tactic.closeMainGoalUsing `toTerm_eTT_symm fun _ _ => do
      return (← Lean.Meta.getLocalDeclFromUserName `termRefl).toExpr



def eFib {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : RT (reY Z Y) (wd Z u) (wd Z u')) :
    fib Y ((eRT Z Y u u').symm t) ≃ fib (reY Z Y) t :=
  ((eTT Z Y u u').symm.subtypeEquiv fun s => by
    rw [toTerm_eTT_symm]
    exact ((eRT Z Y u u').symm.injective.eq_iff).symm).symm



theorem fibFin_re {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (u u' : D.what₂.Word)
    (t : RT (reY Z Y) (wd Z u) (wd Z u')) : Finite (fib (reY Z Y) t) := by
  exact @Finite.of_equiv _ _ (h.fibFin u u' ((eRT Z Y u u').symm t)) (eFib Z Y u u' t)



theorem pairIndep_re {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (u u' : D.what₂.Word)
    (s₁ s₂ s₁' s₂' : TT (reY Z Y) (wd Z u) (wd Z u')) (e₁ : s₁.toTerm = s₁'.toTerm) (e₂ : s₂.toTerm = s₂'.toTerm)
    (r₁ : rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₁ = rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₂)
    (r₂ : rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₁' = rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₂') :
    s0T s₁ s₂ = s0T s₁' s₂' ∧ (liftScalar s₁ s₂ ↔ liftScalar s₁' s₂') := by
  have e₁' : ((eTT Z Y u u').symm s₁).toTerm = ((eTT Z Y u u').symm s₁').toTerm := by
    rw [toTerm_eTT_symm, toTerm_eTT_symm, e₁]
  have e₂' : ((eTT Z Y u u').symm s₂).toTerm = ((eTT Z Y u u').symm s₂').toTerm := by
    rw [toTerm_eTT_symm, toTerm_eTT_symm, e₂]
  let back := (eTT Z Y u u').symm
  have pair := h.pairIndep u u' (back s₁) (back s₂) (back s₁') (back s₂') e₁' e₂'
  run_tac
    -- The row equalities and the conclusion convert by reduction in the kernel.
    Lean.Elab.Tactic.closeMainGoalUsing `pairIndep_re fun _ _ => do
      let localExpr := fun name => return (← Lean.Meta.getLocalDeclFromUserName name).toExpr
      return Lean.mkApp2 (← localExpr `pair) (← localExpr `r₁) (← localExpr `r₂)


set_option maxHeartbeats 16000000 in
theorem finX_reY : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X), FinX Y → FinX (reY Z Y) := by
  intro D Z X Y h
  refine
    { shInj := ?_
      shSurj := ?_
      inHH := ?_
      puLin := ?_
      finHH := ?_
      fibFin := ?_
      pairIndep := ?_
      Greal := fun u u' t => ?_
      cdEx := ?_
      volPos := ?_ }
  run_tac
    -- Elaborate the field proofs independently and let the kernel check their conversion.
    let h := Lean.mkIdent `h
    let Z := Lean.mkIdent `Z
    let Y := Lean.mkIdent `Y
    let u := Lean.mkIdent `u
    let u' := Lean.mkIdent `u'
    let t := Lean.mkIdent `t
    let fields := [
      ← `(FinX.shInj $h),
      ← `(FinX.shSurj $h),
      ← `(FinX.inHH $h),
      ← `(FinX.puLin $h),
      ← `(FinX.finHH $h),
      ← `(fibFin_re $Z $h),
      ← `(pairIndep_re $Z $h),
      ← `(FinX.Greal $h $u $u' ((eRT $Z $Y $u $u').symm $t)),
      ← `(FinX.cdEx $h),
      ← `(FinX.volPos $h)]
    for field in fields do
      Lean.Elab.Tactic.closeMainGoalUsing `finX_reY fun _ _ =>
        Lean.Elab.Term.elabTerm field none

end GlobalTheory.Mem.SRe

end
