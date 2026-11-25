module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA

section
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.Poinc

theorem stalkId_finsetProd {X : Scheme.{0}} {ι : Type} (s : Finset ι) (K : ι → X.IdealSheafData) (x : X) :
    FinalTheorems.stalkId (∏ c ∈ s, K c) x = ∏ c ∈ s, FinalTheorems.stalkId (K c) x := by
  classical
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  simp only [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x ⟨U, hU⟩ hx]
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.prod_insert hc, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul, ih]

theorem stalkId_prodPow {X : Scheme.{0}} {ι : Type} [Fintype ι] (K : ι → X.IdealSheafData) (e : ι → ℕ) (x : X) :
    FinalTheorems.stalkId (∏ c, K c ^ e c) x = ∏ c, FinalTheorems.stalkId (K c) x ^ e c := by
  rw [stalkId_finsetProd]
  simp only [GlobalTheory.Vanishing.stalkId_pow]

end GlobalTheory.Poinc
end
end
end


@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

def UValThru (Xo : Moduli D l) (c : Coeff l) {S T : Scheme.{0}} (i : Xo.XF c ⟶ T) (π : S ⟶ T) (A : Set S)
    (φ : InvFun (𝓞 E)) (J : S.IdealSheafData) (d : ℕ) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ S) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ i = jK W ≫ χ ≫ π → χ (closedPoint W) ∈ A →
    ∀ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))), Nonempty (SABMap tK t (jK W)) →
      Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∀ P : PELUnif (maximalIdeal W) t,
      ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
        ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong J χ = Ideal.span {ϖ ^ n}

variable {Xo : Moduli D l} {c : Coeff l}

theorem uValThru_top_of_disjoint {S : Scheme.{0}} {i : Xo.XF c ⟶ S} {A : Set S} (hA : IsOpen A)
    (hd : A ∩ Set.range i = ∅) (φ : InvFun (𝓞 E)) (d : ℕ) : UValThru Xo c i (𝟙 S) A φ ⊤ d := by
  intro W _ _ _ _ ϖ _ χ y hy hA' _ _ _ _ _ _ _ _
  exfalso
  let g : Sp (FractionRing W) := closedPoint (FractionRing W)
  have hsp : (jK W) g ⤳ closedPoint W := IsLocalRing.specializes_closedPoint _
  have hmem : χ ((jK W) g) ∈ A := (hsp.map χ.continuous).mem_open hA hA'
  have hrange : χ ((jK W) g) ∈ Set.range i := ⟨y g, by
    have := congrArg (fun f => f.base g) hy
    simpa using this⟩
  have : χ ((jK W) g) ∈ A ∩ Set.range i := ⟨hmem, hrange⟩
  rw [hd] at this
  exact this

theorem exists_uValOn_of_pieces {S : Scheme.{0}} (i : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) {ι : Type} [Fintype ι]
    (A : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ) (huniq : ∀ x, ∃! k, x ∈ A k) (hd : ∀ k, 1 ≤ d k)
    (hsupp : ∀ k, ∀ x ∈ (J k).support, x ∈ A k ∧ x ∉ Set.range i)
    (hv : ∀ k, UValThru Xo c i (𝟙 S) (A k) φ (J k) (d k)) :
    ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range i) ∧ UValOn Xo c i φ J' d' := by
  have hdvd : ∀ k, d k ∣ ∏ k, d k := fun k => Finset.dvd_prod_of_mem (s := Finset.univ) d (Finset.mem_univ k)
  have htop : ∀ k x, x ∉ A k → FinalTheorems.stalkId (J k) x = ⊤ := fun k x hx =>
    GlobalTheory.Vanishing.stalkId_eq_top (J k) fun hs => hx (hsupp k x hs).1
  refine ⟨∏ k, d k, ∏ k, J k ^ ((∏ k, d k) / d k), ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => by have := hd k; omega)
  · intro x hx
    obtain ⟨k, hk, -⟩ := huniq x
    by_cases hs : x ∈ (J k).support
    · exact (hsupp k x hs).2
    · exfalso
      refine (mem_support_iff_stalkId _ x).1 hx ?_
      rw [stalkId_prodPow, ← Ideal.one_eq_top]
      refine Finset.prod_eq_one fun k' _ => ?_
      by_cases e : k' = k
      · subst e; rw [GlobalTheory.Vanishing.stalkId_eq_top (J k') hs, ← Ideal.one_eq_top, one_pow]
      · rw [htop k' x fun h => e ((huniq x).unique h hk), ← Ideal.one_eq_top, one_pow]
  · intro W _ _ _ hW ϖ hϖ χ y hy t tK h1 h2 P be hbe hmono
    obtain ⟨k, hk, -⟩ := huniq (χ (closedPoint W))
    obtain ⟨a, ha, hJ⟩ := hv k W hW ϖ hϖ χ y (by rw [Category.comp_id]; exact hy) hk t tK h1 h2 P be hbe hmono
    refine ⟨(∏ k, d k) / d k * a, ?_, ?_⟩
    · have hd0 : (d k : ℝ) ≠ 0 := by have := hd k; positivity
      rw [Nat.cast_mul, Nat.cast_div (hdvd k) hd0, ha]
      field_simp
    · unfold idlAlong at hJ ⊢
      rw [stalkId_prodPow, Finset.prod_eq_single k, Ideal.map_pow, hJ, Ideal.span_singleton_pow, ← pow_mul, mul_comm]
      · intro k' _ e
        rw [htop k' _ fun h => e ((huniq _).unique h hk), ← Ideal.one_eq_top, one_pow]
      · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.UPoinc
