module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory

lemma gtCoord_i_comp_q {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {D D' : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    g'.i ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have : IsProper (thickObj R I e D.P.A).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  have := g.q_hom
  have := g'.i_hom
  exact splitTorus_hom_proper_trivial_local _ D'.X _ _ inferInstance

theorem unifPre_abelianPart_iso :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
      ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R))))
        (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
        ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (e : ℕ),
          ∃ (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A),
            IsMonHom β.hom ∧ (U'.gt e).q ≫ β.hom = (U.gt e).q := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' e
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  have := (U.gt e).q_affine
  have := (U'.gt e).q_affine
  exact flatQuotient_iso_of_same_kernel _ _ _ _ _ _ (U.gt e).q (U.gt e).i (U'.gt e).q (U'.gt e).i
    (U.gt e).q_hom (U.gt e).i_hom (U.gt e).q_flat (U.gt e).q_surj inferInstance (U.gt e).isKernel
    (U'.gt e).q_hom (U'.gt e).i_hom (U'.gt e).q_flat (U'.gt e).q_surj inferInstance
    (U'.gt e).isKernel (gtCoord_i_comp_q hI _ _) (gtCoord_i_comp_q hI _ _)

end GlobalTheory
