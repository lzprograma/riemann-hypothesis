module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90RangeEqNormOneOfIsQuad
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin)

namespace GlobalTheory.Mem.DetLift

theorem det_mul_conj_det {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (ι : B →+* A) {n : ℕ} {g : GL (Fin n) A}
    (hg : g ∈ Formalism.UG.UJ σ ((1 : Matrix (Fin n) (Fin n) B).map ι)) :
    (g : Matrix (Fin n) (Fin n) A).det * σ (g : Matrix (Fin n) (Fin n) A).det = 1 := by
  have h : Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * (1 : Matrix (Fin n) (Fin n) B).map ι * (g : Matrix (Fin n) (Fin n) A) =
      (1 : Matrix (Fin n) (Fin n) B).map ι := hg
  rw [Matrix.map_one _ (map_zero ι) (map_one ι), mul_one] at h
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, Matrix.det_one] at h2
  rw [mul_comm, RingHom.map_det]
  exact h2

theorem exists_isDetLift : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (g : GL (Fin n) (AfE H.F H.E)), g ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → ∃ a : Ideles H.E, IsDetLift (host_cmData R H) g a := by
  intro R H n g hg
  have hr := (DetClass.exists_detClass R H (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
    (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).1
  have hd : Matrix.GeneralLinearGroup.det g ∈ U1 (host_cmData R H).sig :=
    Units.ext (det_mul_conj_det _ _ hg)
  obtain ⟨x, hx⟩ := hr.ge hd
  obtain ⟨a, rfl⟩ := finAf_surjective H.F H.E x
  exact ⟨a, hx⟩

end GlobalTheory.Mem.DetLift
