module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.DecComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PowIne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem no_tors (l : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (u : ℤ_[l]) (hu : u ^ l = 1) : u = 1 := by
  apply _root_.no_tors1 <;> assumption

theorem UpperTheory.inertia_acts_trivially_on_roots_of_unity :
    UpperTheory.V.Sd.S3.MuIne := by
  intro F Ω _ _ _ _ _ l hl h2 A hA s ⟨h1, a, h3⟩
  refine ⟨Rq.powIne F Ω l A hA s h1 _ (pow_pos hl.out.pos a)
    (Subgroup.topologicalClosure_minimal _ (UpperTheory.V.B1.decComm F Ω l A hA) (isClosed_Ine A) h3), ?_⟩
  have h4 : s ^ l ^ a ∈ (cycZ F Ω l).ker := by
    refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_singleton.preimage (continuous_cycZ F Ω l)) h3
    rw [Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  rw [MonoidHom.mem_ker, map_pow] at h4
  have : ∀ (b : ℕ) (u : ℤ_[l]), u ^ l ^ b = 1 → u = 1 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih => intro u hu; exact ih u (no_tors l h2 _ (by rw [← pow_mul, ← pow_succ, hu]))
  exact Units.ext (this a _ (by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]))
