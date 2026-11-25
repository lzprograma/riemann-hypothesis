module

public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Ref

open NumberField IsDedekindDomain

noncomputable section

variable {K : Type} [Field K] [NumberField K]

def vl (la : HeightOneSpectrum (𝓞 K)) (x : K) : ℤ := -WithZero.log (la.valuation K x)

structure PtSys (K : Type) [Field K] [NumberField K] (R : Type) [CommRing R] [Algebra K R] where

  Pt : HeightOneSpectrum (𝓞 K) → Type

  val : ∀ {la}, Pt la → R → EReal

end

end GlobalTheory.CompanionTheory.Ar.Ref
