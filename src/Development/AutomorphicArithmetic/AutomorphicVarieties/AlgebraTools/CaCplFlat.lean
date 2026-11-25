module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
public import Mathlib.RingTheory.Flat.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplUniq
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.Stability

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.flat :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B → Module.Flat R B := by
  intro R _ _ p B _ _ _ h
  haveI := h.isPrime
  haveI : Module.Flat (Localization.AtPrime p) (CplAt R p) := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.Flat R (CplAt R p) := Module.Flat.trans R (Localization.AtPrime p) (CplAt R p)
  obtain ⟨e⟩ := IsCplAt.nonempty_algEquiv R p B (CplAt R p) h (isCplAt_cplAt R p)
  exact Module.Flat.of_linearEquiv e.toLinearEquiv
