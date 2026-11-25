module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.RCellCont

theorem continuity_characters_projection : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (_ : IsCharAF D.host.F ψ) (V : HSp D) (b₀ : HermE D ρ) (b : hermA D t), Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2)) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => yv V b₀ z) ∧ Continuous (fun q : Mx D ρ t × (Mx D V.rank ρ × Mx D V.rank t) => ψ (trA (Matrix.trace (pr b₀ q.1 (yv V b₀ q.2))))) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (qv V b₀ z)) ∧ (∀ T, ‖pch ψ b.1 T‖ = 1) ∧ ∀ u, ‖ψ u‖ = 1 := by
  intro D t ρ ψ hψ V b₀ b
  have hψc : Continuous ψ := hψ.1
  have hψn : ∀ u, ‖ψ u‖ = 1 := hψ.2.1
  have htr : Continuous (trA (D := D)) := by unfold trA; fun_prop
  have hhalf : Continuous (halfTr (D := D)) := by
    unfold halfTr
    exact continuous_const.mul htr
  have hpch : ∀ {n : ℕ} (x : Mx D n n), Continuous (fun T : Mx D n n => pch ψ x T) := by
    intro n x
    unfold pch mm
    exact hψc.comp (hhalf.comp ((continuous_const.matrix_mul continuous_id).matrix_trace))
  have hip : ∀ {a c : ℕ} {X : Type} [TopologicalSpace X] (f : X → Mx D V.rank a) (g : X → Mx D V.rank c),
      Continuous f → Continuous g → Continuous (fun x => ip V (f x) (g x)) := by
    intro a c X _ f g hf hg
    unfold ip mm
    exact (GlobalTheory.MixModel.continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  have hyv : Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => yv V b₀ z) := by
    unfold yv mm
    exact continuous_const.matrix_mul (hip _ _ continuous_fst continuous_snd)
  have hpr : ∀ {p : ℕ} {X : Type} [TopologicalSpace X] (f g : X → Mx D ρ p),
      Continuous f → Continuous g → Continuous (fun x => pr b₀ (f x) (g x)) := by
    intro p X _ f g hf hg
    unfold pr
    exact (GlobalTheory.MixModel.continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  refine ⟨?_, hyv, ?_, ?_, ?_, hψn⟩
  · exact (hpch b.1).comp (hip _ _ continuous_snd continuous_snd)
  · exact hψc.comp (htr.comp (hpr _ _ continuous_fst (hyv.comp continuous_snd)).matrix_trace)
  · have hq : Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => qv V b₀ z) := by
      unfold qv
      set_option synthInstance.maxHeartbeats 200000 in
        exact (hip _ _ continuous_snd continuous_snd).sub (hpr _ _ hyv hyv)
    exact (hpch b.1).comp hq
  · intro T
    unfold pch
    exact hψn _

end GlobalTheory.CompanionTheory.RCellCont

end
