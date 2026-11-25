module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.AbelianTrait

theorem isProper_snd_of_mem_abLocus {S : Scheme.{0}} (G : Over S) [IsSeparated G.hom] [LocallyOfFiniteType G.hom]
    {K : Type} [Field K] (t : Sp K ⟶ S) (p : Sp K) (hp : t p ∈ abLocus G) : IsProper (pullback.snd G.hom t) := by
  let K' := AlgebraicClosure K
  let u : Sp K' ⟶ Sp K := spMap (algebraMap K K')
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have q : Sp K' := (default : PrimeSpectrum K')
  have e : (u ≫ t) q = t p := congrArg (fun z => t z) (Subsingleton.elim (u q) p)
  have h₁ := hp K' (u ≫ t) ⟨q, e⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have h₃ : UniversallyClosed (pullback.snd (pullback.snd G.hom t) u) := by
    rw [← P.isoPullback_hom_snd]
    infer_instance
  have : Nonempty (Sp K') := ⟨q⟩
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t) :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu h₃
  exact ⟨⟩

theorem nonempty_pelUnif_of_abLocus : GlobalTheory.LN.UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → Set.range χ ⊆ abLocus t.G → Nonempty (PELUnif (maximalIdeal W) t') := by
  intro hU E _ _ _ H S t W _ _ _ hW χ t' m hpol hr
  have hG := t'.semi
  have := hG.smooth
  have := hG.separated
  let r : Sp (W ⧸ maximalIdeal W) ⟶ Sp W := spMap (Ideal.Quotient.mk (maximalIdeal W))
  have p : Sp (W ⧸ maximalIdeal W) := (default : PrimeSpectrum (ResidueField W))
  have h₀ : r p ∈ abLocus t'.G := (abLocus_pullback abLocusOne t.semi m.cart.1 (r p)).1 (hr ⟨_, rfl⟩)
  have h₁ : IsProper (pullback.snd t'.G.hom r) := isProper_snd_of_mem_abLocus t'.G (K := ResidueField W) r p h₀
  have := hG.comm
  have := hG.geomConnected
  obtain ⟨P, -⟩ := hU E H W hW t' hpol
    ⟨_, ZJ.isGt_splitExtOfAbelian _ ⟨inferInstance, by
      change Smooth (pullback.snd t'.G.hom r)
      infer_instance, h₁, by
      change GeometricallyConnected (pullback.snd t'.G.hom r)
      infer_instance⟩⟩
  exact ⟨P⟩

end GlobalTheory.AbelianTrait
