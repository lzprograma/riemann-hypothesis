module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart

@[expose] public section

noncomputable section

namespace GlobalTheory.KerJ.CharModel

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

section General

variable {L : Type} [Field L] [NumberField L]

theorem prod_inf_mul_finPart (a : Ideles L) :
    ∃ y : ∀ w : InfinitePlace L, (w.Completion)ˣ, (∏ w, infIdele L w (y w)) * finPartI L a = a := by
  apply _root_.GlobalTheory.Mem.Chr.Determ.exists_prod_inf_mul_finPart

theorem isFin_finPart (a : Ideles L) : IsFinIdele (finPartI L a) := fun _ => rfl

alias isUnitary_of_orderDvd := _root_.Formalism.L2.Host.HChar.isUnitary_of_order

end General

variable {D : D7} {C : CharFrame D} (Dt : DtTied D C) {nch : NChoice D} (Tp : TupTied D C nch)

theorem eDt_finPart (a : Ideles D.host.E) : Dt.eDt (finPartI D.host.E a) = Dt.eDt a := by
  obtain ⟨y, hy⟩ := prod_inf_mul_finPart a
  conv_rhs => rw [← hy]
  rw [map_mul, map_prod, Finset.prod_eq_one fun w _ => Dt.inf w (y w), one_mul]


end GlobalTheory.KerJ.CharModel
