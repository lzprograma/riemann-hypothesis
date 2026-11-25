module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes
public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.Primorial

@[expose] public section

open Finset Nat

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem prime_reciprocal_sum_bound : PrimeRecipSum := by
  exact GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
