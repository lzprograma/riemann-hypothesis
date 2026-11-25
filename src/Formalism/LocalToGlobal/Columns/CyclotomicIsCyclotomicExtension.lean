module

public import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower
public import Formalism.LocalToGlobal.UnitaryNorms.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.UnitaryNorms.AdjoinCycZeta
public import Formalism.LocalToGlobal.Columns.NonDeg
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Divisibility.CoeffLemmas
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.UnitaryNorms.PowValCast, Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostRam, Formalism.LocalToGlobal.UnitaryNorms.ExistsCycAct, Formalism.LocalToGlobal.Columns.CyclotomicIsCyclotomicExtension

-- ===== clump member: Formalism.LocalToGlobal.UnitaryNorms.PowValCast =====
-- clump-header: {"m": "Formalism.LocalToGlobal.UnitaryNorms.PowValCast", "h": "module\n\npublic import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower\npublic import Formalism.LocalToGlobal.UnitaryNorms.Lemmas\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.GroupTheory.Nilpotent\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open IntermediateField NumberField

namespace Formalism.L2.Host

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

section Gauss

variable (q : ℕ) [Fact q.Prime]

variable {q}

end Gauss

end Formalism.L2.Host
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.UnitaryNorms.PowValCast =====

-- ===== clump member: Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostRam =====
-- clump-header: {"m": "Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostRam", "h": "module\n\npublic import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

theorem condN_div_d : H.condN / H.d = H.QS * H.q := by
  obtain ⟨-, hd, -, -, -⟩ := H.hyp
  rw [HostRaw.condN, Nat.mul_div_cancel _ hd.pos]

variable {H}

end HostRaw

namespace HostAx

variable {φ : Frame} (H : HostAx φ)

end HostAx

end Formalism.HC

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostRam =====

-- ===== clump member: Formalism.LocalToGlobal.UnitaryNorms.ExistsCycAct =====
-- clump-header: {"m": "Formalism.LocalToGlobal.UnitaryNorms.ExistsCycAct", "h": "module\n\npublic import Formalism.LocalRingCardinality.DataHost\npublic import Formalism.LocalToGlobal.UnitaryNorms.AdjoinCycZeta\nimport Formalism.LocalToGlobal.UnitaryNorms.Lemmas\npublic import Formalism.LocalToGlobal.UnitaryNorms.PowValCast\nimport Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts\npublic import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostRam\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IntermediateField

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

end Formalism.L2.Host
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.UnitaryNorms.ExistsCycAct =====

-- ===== clump member: Formalism.LocalToGlobal.Columns.CyclotomicIsCyclotomicExtension =====
-- clump-header: {"m": "Formalism.LocalToGlobal.Columns.CyclotomicIsCyclotomicExtension", "h": "module\n\npublic import Formalism.LocalToGlobal.Columns.NonDeg\npublic import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators\npublic import Formalism.LocalToGlobal.Divisibility.CoeffLemmas\npublic import Formalism.LocalToGlobal.UnitaryNorms.ExistsCycAct\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Module IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Host Formalism.FrobeniusOrbits

section SplitGen

open Ideal

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]

end SplitGen

section Split

variable {X : Fields}

end Split

section HostZ

variable {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)

def hwQb (d : ℕ) : Qb := Classical.choose (exists_sqrt (-(d : ℤ)))

theorem hwQb_mem (d : ℕ) : hwQb d ∈ sqrts (-(d : ℤ)) := Classical.choose_spec (exists_sqrt (-(d : ℤ)))

theorem hwQb_sq (d : ℕ) : hwQb d ^ 2 = -(d : Qb) := by
  have h : hwQb d ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := hwQb_mem d
  rw [h]; simp

theorem hwQb_mem_EQ : hwQb H.d ∈ H.EQ :=
  H.KQ_le_EQ (sqrts_sub _ (hwQb_mem H.d))

def hwE : (hostFields H ι LL hE).E := (⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ)

theorem hwE_sq : hwE H ι LL hE ^ 2 = -(H.d : (hostFields H ι LL hE).E) := by
  have h : ((⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ)) ^ 2 = -(H.d : H.EQ) := Subtype.val_injective (by
    show hwQb H.d ^ 2 = _
    rw [hwQb_sq]
    simp)
  exact h

def hwO : 𝓞 (hostFields H ι LL hE).E :=
  ⟨hwE H ι LL hE, IsIntegral.of_pow (n := 2) (by norm_num) (by rw [hwE_sq]; exact (isIntegral_natCast H.d).neg)⟩

def hz (a b : ℤ) : 𝓞 (hostFields H ι LL hE).E :=
  (a : 𝓞 (hostFields H ι LL hE).E) + (b : 𝓞 (hostFields H ι LL hE).E) * hwO H ι LL hE

end HostZ

section CharsGen

variable {X : Fields}

variable {Pr : Primes X}

end CharsGen

section Hecke

variable {X : Fields} {Pr : Primes X} {R : Ranks}


end Hecke

def nd2N : ℕ := 204572886511813553061037407562329625995783655411690436542768105489192394035355663504895707466548678171695054788500010062488923813826764064938234928730947196464262768270018653110228498338042697795156970159903677022807129186961004810571117527615229822789011462114279289419559348825463524785325415815445950503458435921145728668675289394505621558664460319354973532563002004291054537384997546176343222140701606270894674242774158138205418672187221164903157007908864

open Formalism.BasicNotions.Examples₂ (H0)

section Inst

variable (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hLL : cycQ nd2N ≤ LL)

end Inst

section Gen

open ComplexOrder

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Gen


section Inst

variable (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hLL : cycQ nd2N ≤ LL)


end Inst

end Formalism.L2.Col
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.Columns.CyclotomicIsCyclotomicExtension =====
