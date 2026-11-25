module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsExpPush
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHalfChar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.ExCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]; rfl

theorem weilIs_iff {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (s' : Sp ℂ ⟶ S') (s : Sp ℂ ⟶ S) (hs : s = s' ≫ f) (k : ℤ) (x y : Over.mk s' ⟶ t'.G) (x₀ y₀ : Over.mk s ⟶ t.G)
    (c : ℂˣ) (hx : x₀.left = x.left ≫ m.φ) (hy : y₀.left = y.left ≫ m.φ) :
    Out.WeilIs t'.G t'.PP.L k x y (unitOn c) ↔ Out.WeilIs t.G t.PP.L k x₀ y₀ (unitOn c) := by
  subst hs
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  exact weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ t.PP.isLB t'.PP.isLB m.cart hL (Over.mk s') k x y x₀ y₀ _ hx hy

theorem exists_isExp_of_family {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ₀ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ₀ ty) (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (FU.Di i) ty Pe) {R K : Type} [CommRing R] [Field K] (f : R →+* K) (σ : K →+* ℂ)
    (B : PAT H (Sp R)) {y : Sp K ⟶ Xo.X} {t : SAB H (Sp K)} (m : SABMap t Xo.univ.t y) (n : SABMap t B.t (spMap f))
    (hy : spMap σ ≫ y = FU.u i Pe) :
    ∃ eB : (Fin g → ℂ) → (Over.mk (spMap (σ.comp f)) ⟶ B.t.G), IsExp B (σ.comp f) (FU.Di i) ty Pe eB ∧
      ∀ z, ∃ x : Sp ℂ ⟶ t.G.left, x ≫ t.G.hom = spMap σ ∧ x ≫ n.φ = (eB z).left ∧ x ≫ m.φ = (FU.ex i Pe z).left := by
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap σ)) (FU.u i Pe) hy.symm
  obtain ⟨q, hq⟩ := LiePull.exists_pushEquiv n.cart (Over.mk (spMap σ)) (spMap (σ.comp f)) (spMap_comp f σ).symm
  have hp' : ∀ z, (p.symm (FU.ex i Pe z)).left ≫ m.φ = (FU.ex i Pe z).left := fun z => by
    rw [← hp, p.apply_symm_apply]
  refine ⟨fun z => q (p.symm (FU.ex i Pe z)), ⟨hP, ?_, fun z w => ?_,
    q.surjective.comp (p.symm.surjective.comp (FU.ex_onto i Pe hP)), fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩, fun z => ⟨(p.symm (FU.ex i Pe z)).left, Over.w _, (hq _).symm, hp' z⟩⟩
  · have hpb := (IsPullback.of_hasPullback t.G.hom (spMap σ)).paste_horiz m.cart.1
    let c : (Fin g → ℂ) → (Sp ℂ ⟶ pullback t.G.hom (spMap σ)) := fun z =>
      pullback.lift (p.symm (FU.ex i Pe z)).left (𝟙 _) ((Over.w _).trans (Category.id_comp _).symm)
    have hc := ThetaPoint.isHolTo_fibre hpb c (fun z => pullback.lift_snd _ _ _) (by
      have e : (fun z => c z ≫ pullback.fst t.G.hom (spMap σ) ≫ m.cm.F) = fun z => (FU.ex i Pe z).left :=
        funext fun z => by rw [← Category.assoc, pullback.lift_fst]; exact hp' z
      rw [e]
      exact ExpUniqFamily.isHolTo_ex FU i Pe hP)
    have e : (fun z => (q (p.symm (FU.ex i Pe z))).left) = fun z => c z ≫ pullback.fst t.G.hom (spMap σ) ≫ n.φ :=
      funext fun z => by rw [← Category.assoc, pullback.lift_fst]; exact hq _
    rw [e]
    exact isHolTo_comp_hom hc _
  · beta_reduce
    rw [FU.ex_add i Pe hP, map_mul, map_mul]
  · exact (map_eq_one_iff q q.injective).trans ((map_eq_one_iff _ p.symm.injective).trans (FU.ex_ker i Pe hP z))
  · have e : p.symm (FU.ex i Pe z ≫ Xo.univ.t.act.act a) = p.symm (FU.ex i Pe z) ≫ t.act.act a := by
      rw [p.symm_apply_eq]
      apply Over.OverMorphism.ext
      rw [hp, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc]
      exact congrArg (· ≫ _) (hp' z).symm
    apply Over.OverMorphism.ext
    beta_reduce
    rw [FU.ex_lin i Pe hP, e, Over.comp_left, hq, hq, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (n.act a)
  · exact (weilIs_iff n _ _ (spMap_comp f σ).symm k _ _ _ _ c (hq _) (hq _)).1
      ((weilIs_iff m _ _ hy.symm k _ _ _ _ c (hp' _).symm (hp' _).symm).2 (FU.ex_weil i Pe hP k a b c hk hc))

end GlobalTheory.CM.ExCompare
end
