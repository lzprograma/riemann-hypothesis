module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BiInvariantReplaceSameDoubleCosetSums

@[expose] public section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.biInvariant_replace_same_double_coset_sums : DosetSwap := by
  first | exact @GlobalTheory.InertZeta.dosetSwap
