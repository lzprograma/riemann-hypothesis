module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem φc_tc (l : ℕ) [Fact l.Prime] (y : Formalism.Per.Fl l) : φc l (tc l y) = tc l (y ^ l) := by
  unfold φc tc
  rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
  congr 1
  rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

end GlobalTheory.PMon.Gauss
