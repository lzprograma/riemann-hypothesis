module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.LocalToGlobal.HermitianForms.TiedBr
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Formalism.LocalToGlobal.KernelLattices.KerMemPin
public import Formalism.LocalToGlobal.KernelLattices.KerMtPin
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists, Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk

open NumberField Formalism.BasicNotions

variable (D : D7) (u : D.what₂.Word)

abbrev Pt : HLat D.what₂.LL := (D.fm u).ptLat

def IsPsi (Ψ : (D.div.Nu u).V →ₗ[D.what₂.LL] (Pt D u).V) : Prop :=
  ∀ x : (D.div.Nu u).V, (D.fm u).ptEmb (Ψ x) = PsiC (D.mem u).C (D.mem u).A (D.mem u).P (D.eMu u (D.jN u x))

def PsiRat : Prop := ∃ Ψ, IsPsi D u Ψ


open Classical in
def Psi : (D.div.Nu u).V →ₗ[D.what₂.LL] (Pt D u).V := if h : PsiRat D u then h.choose else 0

variable (Am : AmbForm D (RowSide.sharp D))

def IsPer (e : (Pt D u).V ≃ₗ[D.what₂.LL] (MtDual D Am).V) : Prop :=
  ∀ (x : (Pt D u).V) (z : (Mt D Am).V),
    D.what₂.embLL ((show Module.Dual D.what₂.LL (Mt D Am).V from e x) z) =
      (D.mem u).P.period ((D.fm u).ptEmb x) ((D.eMt u).symm (Am.jAmb D.what₂.mu0 z))

def AmbMetric : Prop :=
  ∃ e, IsPer D u Am e ∧ ∀ (v : InfinitePlace D.what₂.LL) (x : (Pt D u).V),
    Formalism.HermitianLatticesTheory.normAt (MtDual D Am).b (MtDual D Am).X v (e x) = Formalism.HermitianLatticesTheory.normAt (Pt D u).b (Pt D u).X v x

end GlobalTheory.Core.Rk

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne", "h": "module\n\npublic import Formalism.LocalToGlobal.HermitianForms.ExtraSym\npublic import Formalism.LocalToGlobal.HermitianForms.TiedBr\npublic import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing\npublic import Formalism.LocalToGlobal.GroupLattices.Joint0\npublic import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt\npublic import Formalism.LocalToGlobal.KernelLattices.InterlaceAll\npublic import Formalism.LocalToGlobal.KernelLattices.KerMemPin\npublic import Formalism.LocalToGlobal.KernelLattices.KerMtPin\npublic import Formalism.LocalToGlobal.KernelLattices.TopPin\npublic import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt\npublic import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal\npublic import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity\npublic import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Cls

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 NumberField IsDedekindDomain Matrix Formalism.UG

def RootsG (D : D7) : Prop :=
  ∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

variable {ex : Extra D L hT Gi Gl K Y cX}

end GlobalTheory.Core.Cls

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne =====
