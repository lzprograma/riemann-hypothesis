module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorus
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
open scoped TensorProduct

namespace GlobalTheory.ArcInputCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusExt

attribute [local instance] gtGroup

section Classes

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

variable (hB : D.TauBimult) (oa : D.OAct O) (F : Type) [Field F] [Algebra (FractionRing R) F]

variable {F} {k : ℕ}

variable {F' : Type} [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem isRatio_ext {p p' : QkPt D F k} {z : F} (h : QkPairing.IsRatio p p' z) :
    QkPairing.IsRatio (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  intro T σ y J hJ
  have e := h T (σ ≫ extMap f hf) y J hJ
  have v : ∀ (g : GtPtF D F) χ, val ((gtExt D f hf g).s χ) σ.left y J = val (g.s χ) (σ ≫ extMap f hf).left y J :=
    fun g χ => (val_corr hJ (((eq_gtExt_iff f hf g _).1 rfl).2 χ) _).trans (val_pull hJ _ _ _)
  have w : gs σ.left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F')).inv.hom (f z)) =
      gs (σ ≫ extMap f hf).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z) := by
    refine Eq.trans (congrArg (gs σ.left y ⊤) ?_) (gs_pull σ.left (spMap f) y ⊤ trivial _)
    exact congrArg (fun g => g.hom z) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  dsimp only [qkExt, qkMk]
  rw [v, v, w, gtExt_b, gtExt_b, ← Category.assoc, ← Category.assoc]
  exact e

theorem weil_ext (k : ℕ) (hk : 1 ≤ k) (p p' : QkPt D F k) (z : F) (h : WeilQkIs D F k p p' z) :
    WeilQkIs D F' k (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  obtain ⟨u, hu⟩ := QkPairing.exists_ratio p p'
  obtain rfl := QkPairing.weil_unique globalFns_holds abelianSchemeLaws_all.2.secTwist hB hk p p' h
    (QkPairing.weil_of_ratio globalFns_holds p p' hu)
  exact QkPairing.weil_of_ratio globalFns_holds _ _ (ζ := Units.map f.toMonoidHom u) (isRatio_ext hB f hf hu)

end Classes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.ArcInputCompare
