module

public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
import GroundTheory.PAdicHodge.ACrisPhi
import GroundTheory.PAdicHodge.BCrisPlusInvariants

@[expose] public section

noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

theorem frob_oD_apply (x : Om l) :
    oD l x = algebraMap (Per6.BdRp l) (Per6.BdR l) (algClToBdR l x) := rfl

theorem frob_qB_coe (z : ℤ_[l]) : qB l (z : ℚ_[l]) = Per6.cB l (algebraMap (AInf ℂ_[l] l)
    (ACris.ACris ℂ_[l] l) (IsPerfectoidField.padicIntToWitt l z)) := by
  apply ιCD_injective
  refine (ιCD_qB _).trans (Eq.trans ?_ (ιCD_cB _).symm)
  rw [cD_apply, ACris.iota_padicInt, frob_oD_apply, AlgHom.commutes]

theorem frob_aB_apply (a : Ainf l) : Per6.aB l a =
    Per6.cB l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l a)) :=
  (RingHom.comp_apply _ _ a).trans (RingHom.comp_apply _ _ _)

theorem frob_coeff_tiltMap (xb : OCb l) (k : ℕ) (y : OC l)
    (h : PreTilt.coeff k xb = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    PreTilt.coeff k (Per6.tiltMap l xb) = Ideal.Quotient.mk _ (Per6.intEquiv l y) :=
  (show PreTilt.coeff k (Per6.tiltMap l xb) = Per6.modPEquiv l (PreTilt.coeff k xb) from rfl).trans
    ((congrArg (Per6.modPEquiv l) h).trans rfl)

theorem frob_ainfMap_teich (xb : OCb l) :
    Per6.ainfMap l (WittVector.teichmuller l xb) = WittVector.teichmuller l (Per6.tiltMap l xb) :=
  WittVector.map_teichmuller l _ _

end PositivityTheory.LocInh
