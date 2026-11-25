module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
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
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open ReciprocityTheory.AnForm.R (ds_stalkId_eq_map)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (cutIdeal)
open H0

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' T : Scheme.{0}} {φ : Y' ⟶ Y}

section Ideal

variable {L : LB Y} {L' : LB Y'} {ι : Type}

theorem secGer_chartSec (l : ChartPull L' L φ) (s : ι → L.Sec) (j : L'.ι) (z : Y') (hj : z ∈ L'.U j)
    (i : ι) : secGer (fun i => chartSec l (s i)) j z hj i =
      (φ.stalkMap z).hom (secGer s (l.idx j) (φ z) (l.le j hj) i) :=
  ger_appLE φ (l.le j) z hj _

theorem stalkId_cutIdeal_chartSec (hL : L.IsLB) (hL' : L'.IsLB) (l : ChartPull L' L φ)
    (s : ι → L.Sec) (z : Y') : stalkId (cutIdeal hL' fun i => chartSec l (s i)) z =
      (stalkId (cutIdeal hL s) (φ z)).map (φ.stalkMap z).hom := by
  obtain ⟨j, hj⟩ := exists_chart hL' z
  rw [stalkId_cutIdeal hL' _ j z hj, stalkId_cutIdeal hL s _ _ (l.le j hj), Ideal.map_span,
    ← Set.range_comp]
  exact congrArg (fun f => Ideal.span (Set.range f)) (funext (secGer_chartSec l s j z hj))

theorem stalkId_cutIdeal_secPull (hL : L.IsLB) (s : ι → L.Sec) (z : Y') :
    stalkId (cutIdeal (LB.isLB_pull hL φ) fun i => secPull (s i) φ) z =
      (stalkId (cutIdeal hL s) (φ z)).map (φ.stalkMap z).hom :=
  stalkId_cutIdeal_chartSec hL _ (GlobalTheory.chartPullPull L φ) s z

variable {I : Y.IdealSheafData} {I' : Y'.IdealSheafData}

theorem le_ker_iff_stalk (t : T ⟶ Y) :
    I ≤ t.ker ↔ ∀ z, stalkId I (t z) ≤ RingHom.ker (t.stalkMap z).hom := by
  refine ⟨fun h z => ?_, fun h => Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_⟩
  · obtain ⟨W, hW, -⟩ := exists_affine (U := ⊤) (y := t z) trivial
    rw [ds_stalkId_eq_map I W _ hW, Ideal.map_le_iff_le_comap]
    intro a ha
    have h₀ : (t.app W.1).hom a = 0 := t.ideal_ker_le W (h W ha)
    exact (Scheme.Hom.germ_stalkMap_apply t _ z hW a).trans ((congrArg _ h₀).trans (map_zero _))
  · refine fun_ext_ger (U := t ⁻¹ᵁ U.1) fun z hz => ?_
    have := h z ((mem_ideal_iff_ger I U a).1 ha _ hz)
    exact (Scheme.Hom.germ_stalkMap_apply t _ z hz a).symm.trans (this.trans (map_zero _).symm)

variable (hI : ∀ z, stalkId I' z = (stalkId I (φ z)).map (φ.stalkMap z).hom)
include hI

theorem le_ker_iff_comp (t : T ⟶ Y') : I' ≤ t.ker ↔ I ≤ (t ≫ φ).ker := by
  rw [le_ker_iff_stalk, le_ker_iff_stalk]
  refine forall_congr' fun z => ?_
  rw [hI, Ideal.map_le_iff_le_comap, RingHom.comap_ker, Scheme.Hom.stalkMap_comp]
  rfl

theorem le_map_of_stalk : I ≤ I'.map φ := (le_ker_iff_comp hI _).1 I'.ker_subschemeι.ge

theorem eq_comap_of_stalk : I' = I.comap φ :=
  le_antisymm ((le_ker_iff_comp hI _).2 (by
      rw [Limits.pullback.condition]
      exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)))
    (Scheme.IdealSheafData.le_map_iff_comap_le.1 (le_map_of_stalk hI))

end Ideal

section Order

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {B : LB Y} {B' : LB Y'} {O : Y.Opens}
  {I : Y.IdealSheafData} {I' : Y'.IdealSheafData} {n : ℕ}
  (hI : ∀ z, stalkId I' z = (stalkId I (φ z)).map (φ.stalkMap z).hom)




end Order

section On

variable {S S' : Scheme.{0}} {u : S ⟶ Y} {u' : S' ⟶ Y'} {ψ : S' ⟶ S}

variable {B : LB Y} {B' : LB Y'}

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {O : Y.Opens} {W : Y'.Opens}
  {I : Y.IdealSheafData} {I' : Y'.IdealSheafData} {ψ : I'.subscheme ⟶ I.subscheme}

end On

theorem LeadAt.map {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    {ι : Type} [Finite ι] {π : R →+* S} {π' : R' →+* S'} {x : ι → R} {a : ℕ} {f : R}
    {γ : MonoDeg ι a → S} (h : LeadAt π x f γ) (θ : R →+* R') (η : S →+* S')
    (e : ∀ r, π' (θ r) = η (π r)) : LeadAt π' (fun i => θ (x i)) (θ f) fun α => η (γ α) := by
  obtain ⟨m, hm, hf⟩ := h
  refine ⟨fun α => θ (m α), fun α => by rw [e, hm], ?_⟩
  have := Ideal.mem_map_of_mem θ hf
  rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at this

  simp only [map_sub, map_sum, map_mul, map_monoVal] at this
  exact this

section Lead

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {L M : LB Y} {L' M' : LB Y'}
  {hL : L.IsLB} {hL' : L'.IsLB} {ι : Type} [Finite ι] {s : ι → L.Sec} {O : Y.Opens} {W : Y'.Opens}

end Lead

section Symbol

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} (H : IsPullback φ p' p (spMap σ))




variable {D : ℕ} [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] (K : CanonLB p D)
  {L A B : LB Y} {L' A' B' : LB Y'} (l : ChartPull L' L φ) (a : ChartPull A' A φ)
  (b : ChartPull B' B φ) (s : Fin D → L.Sec)

abbrev pullQuotSec (e : (LB.div A (tw B L D)).Sec) : (LB.div A' (tw B' L' D)).Sec :=
  chartSec (chartPullQuot a (chartPullTwist b l D)) e

variable (hL : L.IsLB) (hA : A.IsLB) (hB : B.IsLB) (hL' : L'.IsLB) (hA' : A'.IsLB) (hB' : B'.IsLB)
  (e : (LB.div A (tw B L D)).Sec)


variable (hS : Etale ((cutIdeal hL s).subschemeι ≫ p))
  (hS' : Etale ((cutIdeal hL' fun t => chartSec l (s t)).subschemeι ≫ p'))
  (he : SuppIn (nonzeroLocus e) (cutIdeal hL s))
  (he' : SuppIn (nonzeroLocus (pullQuotSec l a b e)) (cutIdeal hL' fun t => chartSec l (s t)))
  {ψ : (cutIdeal hL' fun t => chartSec l (s t)).subscheme ⟶ (cutIdeal hL s).subscheme}
  (hψ : ψ ≫ (cutIdeal hL s).subschemeι = (cutIdeal hL' fun t => chartSec l (s t)).subschemeι ≫ φ)

variable {O : Y.Opens} {W : Y'.Opens} (hW : W ≤ φ ⁻¹ᵁ O) (hO : SuppIn O (cutIdeal hL s))
  (hO' : SuppIn W (cutIdeal hL' fun t => chartSec l (s t)))

end Symbol

section Field

variable {E E' : Type} [Field E] [Field E'] {σ : E →+* E'} {p : Y ⟶ Sp E} {p' : Y' ⟶ Sp E'}
  (H : IsPullback φ p' p (spMap σ)) {L : LB Y} (hL : L.IsLB)




section Order

variable {ι : Type} (s : ι → L.Sec) {B : LB Y} {B' : LB Y'} {O : Y.Opens} {n : ℕ}

end Order

variable {D : ℕ} [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] (K : CanonLB p D)
  {A B : LB Y} {A' B' : LB Y'} (hA : A.IsLB) (hB : B.IsLB) (hA' : A'.IsLB) (hB' : B'.IsLB)
  (a : ChartPull A' A φ) (b : ChartPull B' B φ) (s : Fin D → L.Sec)
  (hS : Etale ((cutIdeal hL s).subschemeι ≫ p)) (e : (LB.div A (tw B L D)).Sec)
  (he : SuppIn (nonzeroLocus e) (cutIdeal hL s)) {O : Y.Opens} (hO : SuppIn O (cutIdeal hL s))

end Field

end GlobalTheory.Vanishing
