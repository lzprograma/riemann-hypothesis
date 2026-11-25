module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq

@[expose] public section

noncomputable section

namespace GlobalTheory.Equiv.StdSpace

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct Matrix

variable {D : D7}

theorem coe_pi_one_eq_intVecs (n : ℕ) :
    ((Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) :
      Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.intVecs D n := by
  ext x
  rw [SetLike.mem_coe, Submodule.mem_pi]
  exact ⟨fun k a => Submodule.mem_one.1 (k a trivial), fun k a _ => Submodule.mem_one.2 (k a)⟩

theorem identityClassLattice_eq_selfDualFrameLattice (V : HSp D) : (Bridge.hLat V 1 : Set (Fin V.rank → D.host.E)) = L0c D V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg hsp).1
  rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.coe_set_eq]
  unfold Bridge.hLat
  rw [← Submodule.span_eq (GlobalTheory.Member.latC V)]
  congr 1
  ext x
  rw [SetLike.mem_coe, ← key x, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq,
    show ((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) = 1 from Subtype.ext inv_one]
  show (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ _ ∈
    Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ _
  rw [Matrix.one_mulVec]
  exact Iff.rfl

theorem lattice_clause_iff (V : HSp D) :
    (Bridge.hLat V 1 = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) ↔
      L0c D V = GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.intVecs D V.rank := by
  rw [← identityClassLattice_eq_selfDualFrameLattice, ← coe_pi_one_eq_intVecs, SetLike.coe_set_eq]

end GlobalTheory.Equiv.StdSpace

end
