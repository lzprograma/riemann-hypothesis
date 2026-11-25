module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

abbrev OC : Type := ↥(PadicComplexInt l)
abbrev NC : Type := ↥(normInteger ℂ_[l])

abbrev e : OC l ≃+* NC l := Formalism.Per6.intEquiv l

/-- Functoriality of `Acris` applied to the two presentations of the integers of `ℂ_[l]`. -/
def cA : Reformulated.AutPerF.Acris l (OC l) ≃+* ACris.ACris ℂ_[l] l :=
  RingEquiv.ofRingHom (Reformulated.AutPerF.Acris.map l (e l).toRingHom)
    (Reformulated.AutPerF.Acris.map l (e l).symm.toRingHom)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.id_apply, Reformulated.AutPerF.Acris.map_map,
        show (e l).toRingHom.comp (e l).symm.toRingHom = RingHom.id _ from
          RingHom.ext fun y => (e l).apply_symm_apply y, Reformulated.AutPerF.Acris.map_id])
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.id_apply, Reformulated.AutPerF.Acris.map_map,
        show (e l).symm.toRingHom.comp (e l).toRingHom = RingHom.id _ from
          RingHom.ext fun y => (e l).symm_apply_apply y, Reformulated.AutPerF.Acris.map_id])

theorem cA_apply (x : Reformulated.AutPerF.Acris l (OC l)) :
    cA l x = Reformulated.AutPerF.Acris.map l (e l).toRingHom x := rfl

end Cmp6
