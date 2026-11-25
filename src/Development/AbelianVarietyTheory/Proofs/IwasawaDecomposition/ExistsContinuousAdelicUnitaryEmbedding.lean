module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.UnitaryEmb

open scoped TensorProduct
open NumberField Matrix

section General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (B A : HSpace E) (ι : B.V →ₗ[E] A.V) (h : HSpace.IsIsomEmb B A ι)

theorem continuous_embA : Continuous (embA hc B A ι h) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine Continuous.subtype_mk (Continuous.comp (g := Units.map _) ?_ continuous_subtype_val) _
  exact Continuous.units_map _ (continuous_const.add
    ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const))

theorem embA_ratA (γ : GRat hc B) : embA hc B A ι h (ratA hc B γ) = ratA hc A (embRat hc B A ι h γ) := by
  refine Subtype.ext (Units.ext ?_)
  show 1 + (embMat B A ι).map (inclR (F := F) (AF F)) *
      (((γ : GL (Fin B.rank) E) : Matrix (Fin B.rank) (Fin B.rank) E).map (inclR (F := F) (AF F)) - 1) *
        (projMat hc B A ι).map (inclR (F := F) (AF F)) =
    (1 + embMat B A ι * (((γ : GL (Fin B.rank) E) : Matrix (Fin B.rank) (Fin B.rank) E) - 1) *
      projMat hc B A ι).map (inclR (F := F) (AF F))
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

theorem exists_embHom (D : D7) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (hι : HSpace.IsIsomEmb B A ι) :
    ∃ s : GA D B →* GA D A, Continuous s ∧ (∀ h g, EmbRel A B ι g h ↔ g = s h) ∧ ∀ γ ∈ GQ B, s γ ∈ GQ A := by
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embA D.sp.cm B A ι hι, continuous_embA D.sp.cm B A ι hι,
    fun h g => GlobalTheory.AutFunCompare.embRel_iff A B ι hι g h, ?_⟩
  rw [GlobalTheory.AutFunCompare.GQ_eq, GlobalTheory.AutFunCompare.GQ_eq]
  rintro _ ⟨γ, rfl⟩
  exact ⟨_, (embA_ratA D.sp.cm B A ι hι γ).symm⟩

end GlobalTheory.Mem.UnitaryEmb

end
