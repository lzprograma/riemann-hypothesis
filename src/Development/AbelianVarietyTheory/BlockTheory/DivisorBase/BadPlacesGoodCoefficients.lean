module

public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.BadPlacesGoodCoefficients

variable {D : D7}

def badPlaces (D : D7) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  Formalism.L2.DIV.primesOf (((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F))

def IsBelow {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (b : Pg ≃ LevelCuspCharacters.Sq D.host) : Prop :=
  ∀ PP : Pg, (b PP).2.1.asIdeal = PP.1.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))

def IsFrameAtG (V : HSp D) (β : GL (Fin V.rank) (EAf D)) : Prop :=
  ∃ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ), IsBaseFrame V β Λ ((D.host.g 0 * D.host.g 1) ^ c)

def datR (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ)
    (fr : Lev.Frm) : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank :=
  datY V.rank D.R.r D.R.t 0 hr Pg ∅ P (fun _ _ => 1) (fun _ => 1) fr

def eLin (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (e : Formalism.L2.DIV.G0 L.Pg L.r →₀ ℂ) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := eAct V β L e
  map_add' F G := by
    funext h
    simp only [eAct, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  map_smul' a F := by
    funext h
    simp only [eAct, Finsupp.sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp

theorem rank_le_first_space_rank (D : D7) : D.R.r ≤ (D.sp.Y 0).rank := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Ranks.rankY]

section Parts

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}

def rowPart (M : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (β : GL (Fin (D.sp.Y 0).rank) (EAf D))
    (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ) (e : Formalism.L2.DIV.G0 Pg D.R.r →₀ ℂ)
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  EEpart θ M (levG (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B) : Set (GA D (D.sp.Y 0)))
    (levChi (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B))
    (eLin (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B) e) (badPlaces D) c

end Parts

def gramIn (V : HSp D) (β : GL (Fin V.rank) (EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (EAf D) :=
  Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) β.val *
    V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * β.val

end GlobalTheory.IndefiniteRowSideFullHecke.BadPlacesGoodCoefficients

end
