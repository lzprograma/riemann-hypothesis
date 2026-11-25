module

public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GlR
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GLRealOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Measure Topology Matrix

namespace Formalism.DoubleCosetMeasures.P

namespace GeneralLinearIntegersOpenCompact

section Alg

variable {K : Type} [CommRing K]

noncomputable def glR (R : Subring K) (n : ℕ) : Subgroup (GL (Fin n) K) :=
  _root_.UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR R n

end Alg

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem glR_compact [T2Space K] (R : Subring K) (hR : IsCompact (R : Set K)) (n : ℕ) :
    IsCompact (glR R n : Set (GL (Fin n) K)) := by
  let S : Set (Matrix (Fin n) (Fin n) K) :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => (R : Set K)))
  have hS : IsCompact S := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => hR))
  have hS' : IsCompact (MulOpposite.unop ⁻¹' S : Set (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.isCompact_preimage.mp hS
  have := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS.prod hS')
  convert this using 1
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a _ b _ => h1 a b, fun a _ b _ => h2 a b⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a b => h1 a (Set.mem_univ _) b (Set.mem_univ _),
      fun a b => h2 a (Set.mem_univ _) b (Set.mem_univ _)⟩

end Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

end GeneralLinearIntegersOpenCompact

open GeneralLinearIntegersOpenCompact

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

end Formalism.DoubleCosetMeasures.P
