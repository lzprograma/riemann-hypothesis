module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
public import Mathlib.NumberTheory.NumberField.CMField

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.F.Small

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem countable_pl (E : Type) [Field E] [NumberField E] : Countable (HeightOneSpectrum (𝓞 E)) := by
  apply _root_.GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum <;> assumption

end PositivityTheory.Rg.BcB.F.Small

end
