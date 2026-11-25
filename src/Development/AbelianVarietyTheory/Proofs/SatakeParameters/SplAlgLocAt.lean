module

public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulVecMemColSpan
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
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV.LbB

section Inst

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}

theorem locInt_locAt (B : GL (Fin D.R.k) D.host.E) : LocInt (locAt X u w hg B) := by
  intro v x
  exact (X.g u w hg).completion_integers_iff v _ rfl x

theorem splAlg_locAt (B : GL (Fin D.R.k) D.host.E) : GlobalTheory.TwV.SplAlg (locAt X u w hg B) := by
  intro v a
  exact (X.g u w hg).spl_alg _ _ a

theorem reL_eq_map {a b : ℕ} (h : a = b) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) :
    reL h L = L.map (((Formalism.L2.PairingIndexBounds.F.reE (E := D.host.E) h : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) :
      (Fin a → D.host.E) →ₗ[D.host.E] (Fin b → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  subst h
  rfl



theorem lbAtB_locAt (B : GL (Fin D.R.k) D.host.E) (hrat : FrRat X u w hg B) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E))
    (hL : L = reL (rank_eq_first_level D.R) (X.lev0 u).Lb) : GlobalTheory.TwV.LbAtB (locAt X u w hg B) L := by
  rw [hL, reL_eq_map]
  exact lbAtB_of _ (locInt_locAt B) (splAlg_locAt B) _
    (frAtB_re (rank_eq_first_level D.R) (locAt X u w hg B) (X.lev0 u).Lb B rfl (fun v => (X.g u w hg).fr _ ((X.g u w hg).pl v).2)
      (fun v tt => (X.g u w hg).fr_lat _ _ tt) (fun v => hrat _ _))

end Inst

theorem lbAtB_lev0At : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Joint0 g.herm.lev0 u (g.forms u) → GlobalTheory.TwV.LbAtB (lev0At g u w hg).A (lev0At g u w hg).Lb := by
  intro D Gt c g u w hg hJ
  exact lbAtB_locAt g.cmp.B (g.cmp.fr_B u w hg) _ hJ.Lb_eq

end GlobalTheory.TwV.LbB

end
