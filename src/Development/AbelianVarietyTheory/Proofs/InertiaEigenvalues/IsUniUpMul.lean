module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

@[expose] public section

namespace GlobalTheory.UnipotentUpperMul

theorem isUniUp_mul : ∀ {R : Type} [inst : CommRing R] {N : ℕ} {M M' : Matrix (Fin N) (Fin N) R},
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp M → Formalism.MainNotions.ArithmeticCylinders.IsUniUp M' → Formalism.MainNotions.ArithmeticCylinders.IsUniUp (M * M') := by
  apply GlobalTheory.BadCount.Inh.isUniUp_mul

end GlobalTheory.UnipotentUpperMul
