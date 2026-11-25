module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.GoodTrait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_of_point {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ)
    {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = x ≫ χ) : PolAt t x := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull x t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t' : SAB H (Sp K)) (p : Sp K ⟶ Y.X) (_ : p = y ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t y) := by
    intro t' p hp n
    subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ hy.symm n
  have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem splitOver_of_abLocus {W : Type} [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) (h : ∀ x, x ∈ abLocus G) : GlobalTheory.LN.SplitOver G (maximalIdeal W) := by
  letI := Ideal.Quotient.field (maximalIdeal W)
  have p : Spec (CommRingCat.of (W ⧸ maximalIdeal W)) := (default : PrimeSpectrum _)
  have hp := ArcNotAbelian.isProper_fibre G hG (W ⧸ maximalIdeal W) (spMap (Ideal.Quotient.mk (maximalIdeal W))) p (h _)
  have := hG.comm
  have := hG.smooth
  have := hG.geomConnected
  have hab : IsAbelianScheme ((Over.pullback (spMap (Ideal.Quotient.mk (maximalIdeal W)))).obj G) :=
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)), hp,
      inferInstanceAs (GeometricallyConnected (pullback.snd _ _))⟩
  unfold GlobalTheory.LN.SplitOver
  exact ⟨_, ZJ.isGt_splitExtOfAbelian _ hab⟩

theorem exists_pelUnif_subsingleton : LL → UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ Y.j = jK W ≫ χ → Set.range χ ⊆ abLocus Y.t.G → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t), Subsingleton P.D.toPre.X := by
  intro _ hU E _ _ _ H D l Xo c O _ β Y W _ _ _ hW χ y hy hab
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp W), Nonempty (SABMap t Y.t χ) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull χ Y.t
    exact ⟨_, ⟨m⟩⟩
  have ht : ∀ x, x ∈ abLocus t.G := fun x => (abLocus_pullback abLocusOne Y.t.semi m.cart.1 x).1 (hab ⟨x, rfl⟩)
  obtain ⟨P, -⟩ := hU E H W hW t (polAt_of_point Y m _ y hy) (splitOver_of_abLocus t.G t.semi ht)
  refine ⟨t, m, P, ?_⟩
  have hmax : (maximalIdeal W ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (W ⧸ maximalIdeal W ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (W ⧸ maximalIdeal W ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (W ⧸ maximalIdeal W ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick W (maximalIdeal W) 0) p (ht _)
    P.D.toPre.X g.i g.i_hom

end GlobalTheory.GoodTrait
