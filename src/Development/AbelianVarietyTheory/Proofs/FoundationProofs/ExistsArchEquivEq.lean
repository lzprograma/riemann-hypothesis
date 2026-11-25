module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
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

namespace GlobalTheory.AdelicU

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

def placeOf (D : D7) (ρ : D.what₂.Tau) : InfinitePlace D.host.F :=
  InfinitePlace.mk ((tauE D ρ).comp (algebraMap D.host.F D.host.E))

theorem placeOf_bijective (D : D7) : Function.Bijective (placeOf D) := GlobalTheory.CMTypePlaces.places_bijective D

def embOverOf (D : D7) (ρ : D.what₂.Tau) : EmbOver D.host.E (placeOf D ρ) :=
  ⟨tauE D ρ, by
    have := (isCMExt_host D).1
    exact (InfinitePlace.embedding_mk_eq_of_isReal
      (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (placeOf D ρ)))).symm⟩

@[simp] theorem embOverOf_val (D : D7) (ρ : D.what₂.Tau) : (embOverOf D ρ).1 = tauE D ρ := rfl

theorem isInfFam_infProj (D : D7) : IsInfFam (D := D) fun ρ : D.what₂.Tau => infProj (embOverOf D ρ) :=
  fun ρ => isInfEmb_infProj (embOverOf D ρ)

theorem exists_isInfFam (D : D7) : ∃ θ, IsInfFam (D := D) θ := ⟨_, isInfFam_infProj D⟩

variable {D : D7}

theorem eq_placeOf {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) :
    w = placeOf D ρ := by
  rw [placeOf, ← hτ, τ.2, InfinitePlace.mk_embedding]

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem eq_infProj (hθ : IsInfFam θ) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w)
    (hτ : τ.1 = tauE D ρ) : θ ρ = infProj τ :=
  GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hθ ρ) (hτ ▸ isInfEmb_infProj τ)

theorem isAtTau_embArch (hθ : IsInfFam θ) (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    IsAtTau θ V ρ (archEquiv V.gram (isCMExt_host D) τ x).1.1 (embArch D.sp.cm.sig V.gram w x) := by
  refine ⟨mem_infPts.2 (projFin_embArch _ _ w x), ?_, fun ρ' h => ?_⟩
  · rw [eq_infProj hθ τ hτ, infMat_infProj V.gram (isCMExt_host D), projArch_embArch_self]
  · have hw : placeOf D ρ' ≠ w := fun e => h ((placeOf_bijective D).1 (e.trans (eq_placeOf τ hτ)))
    rw [eq_infProj hθ (embOverOf D ρ') rfl, infMat_infProj V.gram (isCMExt_host D), projArch_embArch_ne _ _ hw,
      map_one]
    rfl

theorem archEquiv_mem_UH (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    (archEquiv V.gram (isCMExt_host D) τ x).1.1 ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  have h := (archEquiv V.gram (isCMExt_host D) τ x).2
  rw [gramAt, ← hτ]
  exact h

theorem exists_archEquiv_eq (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) :
    ∃ x : GArch D.sp.cm.sig V.gram w, (archEquiv V.gram (isCMExt_host D) τ x).1.1 = g := by
  obtain ⟨θ, hθ⟩ := exists_isInfFam D
  obtain ⟨h, hh, -⟩ := GlobalTheory.PointAtPlace.existsUnique_isAtTau V ρ θ hθ g hg
  refine ⟨projArch _ _ w h, ?_⟩
  rw [← infMat_infProj, ← eq_infProj hθ τ hτ]
  exact hh.2.1

theorem atTau_archEquiv (hθ : IsInfFam θ) (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    atTau θ V ρ (archEquiv V.gram (isCMExt_host D) τ x).1.1 = embArch D.sp.cm.sig V.gram w x := by
  have hu := GlobalTheory.PointAtPlace.existsUnique_isAtTau V ρ θ hθ _ (archEquiv_mem_UH V τ hτ x)
  refine hu.unique ?_ (isAtTau_embArch hθ V τ hτ x)
  unfold atTau
  rw [dite_eq_left hu.exists]
  exact hu.exists.choose_spec

end GlobalTheory.AdelicU

end
