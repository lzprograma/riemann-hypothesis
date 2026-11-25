module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.Poinc.Sep.ConjPt

open GlobalTheory.UT.SymFrame

section Tools

variable {X Y Y' : Scheme.{0}} {L : LB X}

theorem exists_powSec (hL : L.IsLB) {K K₃ K' : Type} [Fintype K] [Fintype K₃] [Fintype K'] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (N : ℕ) {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (φ' : K' → (Y' ⟶ X)) (ε' : K' → ℤ)
    (hF : ∀ (U : Type) [CommGroup U] (f : (Y' ⟶ X) → U),
      (∏ k, f (h ≫ φ k) ^ ε k) ^ N * ∏ k, f (φ₃ k) ^ ε₃ k = ∏ k, f (φ' k) ^ ε' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε'), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J ^ N * (val u r z J).val := by
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := φ') (ε' := ε') (fun U _ f => by
      rw [← hF U f, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin])
    (pullMulSec (H1.SectionArithmetic.powSec (fun _ : Fin N => s)) h u hu)
  refine ⟨s', fun Z r z J hJ => ?_⟩
  rw [hs' Z r z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, H1.SectionArithmetic.sval_powSec _ _ _ hJ]
  simp

theorem exists_fn (s : LB.Sec (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) :
    ∃ a : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), sval s r z J = gs r z ⊤ a := by
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Y.presheaf.map (homOfLE le).op).hom (s.f PEmpty.elim), fun Z r z J => ?_⟩
  rw [sval_of s r z J PEmpty.elim (fun k => k.elim)]
  exact (gs_res r z le trivial _).symm

theorem grep_const (hL : L.IsLB) {S : Scheme.{0}} {B : Over S} (e : S ⟶ B.left) (he : e ≫ B.hom = 𝟙 S)
    (hp : Function.Surjective B.hom.appTop.hom) {P v} (h : GRep L B P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : (B.left ⟶ X) → U), P U h = 1) :
    ∃ a : Γ(S, ⊤)ˣ, ∀ (T : Over S) (r : T ⟶ B) (z : T.left) (J), Good L z J → v T r z J = gm T.hom z ⊤ a := by
  obtain ⟨K, _, φ, ε, s, hs, h₁, h₂⟩ := h
  obtain ⟨a, ha⟩ := SymLiftOdd.exists_const hL B.hom e he hp (fun U _ h => (h₁ U h).trans (hP U h)) hs
  exact ⟨a, fun T r z J hJ => by rw [← h₂ T r z J hJ, ha _ _ z J hJ, Over.w]⟩

theorem grep_unit {S : Scheme.{0}} (B : Over S) (a : Γ(S, ⊤)ˣ) :
    GRep L B (fun _ _ _ => 1) (fun T _ z _ => gm T.hom z ⊤ a) := by
  refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ⟨fun _ => res le_top (pullU B.hom ⊤ a)⟩, fun i j => ?_,
    fun _ _ _ => Fintype.prod_empty _, fun T r z J _ => ?_⟩
  · refine Eq.trans ?_ ((congrArg₂ (· * ·) (Fintype.prod_empty _) rfl).trans (_root_.one_mul _)).symm
    exact unit_ext fun y hy => ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.1 _)).trans
      ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.2 _)).symm
  · refine (gm_res r.left z le_top (Set.mem_iInter.2 fun k => k.elim) _).trans ((gm_pull r.left B.hom z ⊤ trivial a).trans ?_)
    rw [Over.w]

end Tools

section Theta

open GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank GlobalTheory.CoordSep

variable {S : Scheme.{0}} (P : PolAV S)

abbrev Th : Type := LB.Sec (LB.LinComb P.L (fun _ : Fin 1 => 𝟙 P.A.left) (fun _ => 1))

def GenAll (θ : Th P) : Prop :=
  ∀ (K : Type) [Field K] (s : Sp K ⟶ S) (t : LB.Sec (LPow P.A P.L 1 (Over.mk s))), ∃ c : Γ(Sp K, ⊤),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk s ⊗ P.A).left) (z : Z) (J), Good P.L z J →
      sv P.A t r z J = gs (r ≫ (fst (Over.mk s) P.A).left) z ⊤ c * sval θ (r ≫ (snd (Over.mk s) P.A).left) z J

theorem exists_genAll {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (P : PolAV (Sp V)) :
    ∃ θ : Th P, GenAll P θ := by
  obtain ⟨U, hU, b, hb⟩ := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange (Sp V) P 1 le_rfl (closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  let T₀ : Over (Sp V) := overRes (T := baseOver (Sp V)) ⊤
  let h : ∀ T : Over (Sp V), T ⟶ T₀ := fun T => Over.homMk (IsOpenImmersion.lift (⊤ : (Sp V).Opens).ι T.hom (by
      rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial))
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  have hu : ∀ {T : Over (Sp V)} (a a' : T ⟶ T₀), a = a' := fun a a' => by
    apply Over.OverMorphism.ext
    rw [← cancel_mono (⊤ : (Sp V).Opens).ι]
    have e := Over.w a
    have e' := Over.w a'
    exact (congrArg (_ ≫ ·) (Category.comp_id _).symm).trans ((e.trans e'.symm).trans
      (congrArg (_ ≫ ·) (Category.comp_id _)))
  let i : Fin (1 ^ P.g) := ⟨0, by simp⟩
  obtain ⟨θ, hθ⟩ := exists_sec P.isLB (φ' := fun _ : Fin 1 => 𝟙 P.A.left) (ε' := fun _ => 1)
    (fun U _ f => Finset.prod_congr rfl fun _ _ => by
      rw [← Over.comp_left, lift_snd]; rfl)
    (H1.SectionArithmetic.pullSec (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) (b i)
      (lift (h P.A) (𝟙 P.A)).left)
  refine ⟨θ, fun K _ s t => ?_⟩
  haveI : IsAffine (Over.mk s).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  obtain ⟨c, hc⟩ := exists_basis P 1 b hb (Over.mk s) (h _)
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  have e := c.sum_repr (SecM.ofSec P.A t)
  rw [Fintype.sum_subsingleton _ i, hc] at e
  refine ⟨c.repr (SecM.ofSec P.A t) i, fun Z r z J hJ => ?_⟩
  have q := ThetaAct.sv_smul (c.repr (SecM.ofSec P.A t) i)
    (pullM P.A P.L ((1 : ℕ) : ℤ) (h (Over.mk s)) (SecM.ofSec P.A (b i))) r z hJ
  refine ((congrArg (fun w => ThetaAct.sv w r z J) e).symm.trans q).trans (congrArg (_ * ·) ?_)
  refine (sv_pullS P.A _ (h _) (b i) r z hJ).trans ?_
  refine Eq.trans ?_ ((hθ _ _ z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ)).symm
  rw [Category.assoc, ← Over.comp_left]
  refine congrArg (fun q : Over.mk s ⊗ P.A ⟶ T₀ ⊗ P.A => sv P.A (b i) (r ≫ q.left) z J) ?_
  apply CartesianMonoidalCategory.hom_ext
  · exact hu _ _
  · simp

abbrev psiLB (N : ℕ) (b : 𝟙_ (Over S) ⟶ P.A) : LB P.A.left :=
  LB.LinComb P.L ![𝟙 P.A.left, ((toUnit P.A ≫ b) * 𝟙 P.A).left] ![(N : ℤ), -(N : ℤ)]

theorem comp_transl {T : Over S} (x : T ⟶ P.A) (b : 𝟙_ (Over S) ⟶ P.A) :
    x.left ≫ ((toUnit P.A ≫ b) * 𝟙 P.A).left = ((toUnit T ≫ b) * x).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

end Theta

section Integral

open GlobalTheory.UT.CoefBasic GlobalTheory.TorusExt GlobalTheory.VVRank

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

theorem grep_cubProd {Y : Over (Sp V)} (c b : Y ⟶ D.P.A) (n : ℕ) :
    GRep D.P.L Y
      (fun _ _ h => h (c * b ^ n).left * (h (b ^ n).left)⁻¹ * (h c.left)⁻¹ * h (1 : Y ⟶ D.P.A).left *
        ((h (c * b).left)⁻¹ * h c.left * h b.left * (h (1 : Y ⟶ D.P.A).left)⁻¹) ^ n)
      (fun _ r z J => ∏ i ∈ Finset.range n, cubV D.cub z J (r ≫ c) (r ≫ b ^ i) (r ≫ b)) := by
  induction n with
  | zero =>
    exact ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen D.P.L, Frames.oneGen_gen _,
      fun _ _ _ => by simp, fun _ _ _ _ _ => by simp [val_one]⟩
  | succ n ih =>
    refine (ih.mul (SymFrame.grep_cub c (b ^ n) b)).congr (fun _ _ h => ?_)
      (fun _ _ _ _ _ => (Finset.prod_range_succ _ _).symm)
    rw [_root_.mul_assoc c, ← pow_succ b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

theorem exists_gen_local [IsLocalRing V] {K : Type} [Fintype K] (φ : K → (Sp V ⟶ D.P.A.left)) (ε : K → ℤ) :
    ∃ t : LB.Gen (LB.LinComb D.P.L φ ε), t.IsGen := by
  choose i hi using fun k => exists_chart D.P.isLB (φ k (closedPoint V))
  exact AbSquare.exists_gen_of_mem_chart D.P.isLB φ ε i fun k y => by
    have : φ k ⁻¹ᵁ D.P.L.U (i k) = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 (hi k)
    exact (this.ge trivial : y ∈ φ k ⁻¹ᵁ D.P.L.U (i k))

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_psi [IsLocalRing V] [IsNoetherianRing V] [IsIntegrallyClosed V] {N : ℕ} (hN : 1 ≤ N)
    (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A)
    (hgb : g.b = toUnit _ ≫ b) (ho : ∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero)
    (w : Frm D (FractionRing V) 1 g.b)
    (hw : w.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1) :
    ∃ Ψ : LB.Gen (psiLB D.P N b), Ψ.IsGen ∧
      (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ (T : Over (Sp V)) (z : T.left) (J),
        Good D.P.L z J → val Ψ (1 : T ⟶ D.P.A).left z J ^ N * val κ (toUnit T ≫ b).left z J = 1) ∧
      ∀ χ z J, Good D.P.L z J → val Ψ (toUnit (TF (R := V) (FractionRing V)) ≫ D.c χ).left z J =
        (val (g.s χ) (𝟙 _) z J * val w (𝟙 _) z J) ^ N := by
  have hL := D.P.isLB
  obtain ⟨hgN, hbN⟩ := Frames.torsion_of_nsmul g b hgb ho
  obtain ⟨t, ht⟩ := exists_gen_local (D := D) ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)
  obtain ⟨u, hu, -⟩ := Frames.frame_unit hN g b hgb ho w hw t ht
  let a : Γ(Sp V, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.toMonoidHom u
  have ha : ∀ z J, Good D.P.L z J → val w (𝟙 _) z J = gm (TF (R := V) (FractionRing V)).hom z ⊤ a *
      val t (TF (R := V) (FractionRing V)).hom z J := fun z J hJ => Units.ext (by
    rw [hu z J hJ, Units.val_mul]
    refine congrArg (· * _) (Eq.trans ?_ (Frames.gm_top_eq a z).symm)
    congr 2
    exact ((Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.apply_symm_apply _).symm)
  obtain ⟨Ψ, hΨ, vΨ⟩ := ((grep_cubProd (𝟙 D.P.A) (toUnit _ ≫ b) N).mul
    (((grep_unit D.P.A a).mul (grep_gen t ht D.P.A.hom)).pow N)).out hL
    ![𝟙 D.P.A.left, ((toUnit D.P.A ≫ b) * 𝟙 D.P.A).left] ![(N : ℤ), -(N : ℤ)] (fun U _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, ← MonObj.comp_pow, hbN, MonObj.comp_one, _root_.mul_one,
        mul_comm (𝟙 D.P.A)]
      show _ * (1 * (h (1 : D.P.A ⟶ D.P.A).left ^ ((1 : ℕ) : ℤ) * h (toUnit _ ≫ b).left ^ (-((1 : ℕ) : ℤ)))) ^ N =
        h (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (N : ℤ) * h ((toUnit D.P.A ≫ b) * 𝟙 D.P.A).left ^ (-(N : ℤ))
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
      push_cast
      module)
  have v1 : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
      val Ψ (1 : T ⟶ D.P.A).left z J = (gm T.hom z ⊤ a * val t T.hom z J) ^ N := fun T z J hJ => by
    have C : IsCub (cubV D.cub (T := T) z J) := isCub_cubV D.cub hJ
    rw [vΨ T 1 z J hJ]
    rw [Over.w, Category.comp_id, Finset.prod_eq_one fun i _ => C.face _ _, _root_.one_mul]
  refine ⟨Ψ, hΨ, fun κ hκ T z J hJ => ?_, fun χ z J hJ => ?_⟩
  · obtain ⟨x, hx⟩ := grep_const hL (B := 𝟙_ (Over (Sp V))) (𝟙 _) (Category.id_comp _) (fun a => ⟨a, rfl⟩)
      (((grep_gen Ψ hΨ (1 : 𝟙_ (Over (Sp V)) ⟶ D.P.A).left).pow N).mul (grep_kap κ hκ.1 b)) (fun U _ h => by
        rw [Fin.prod_univ_two, hbN]
        show (h ((1 : 𝟙_ (Over (Sp V)) ⟶ D.P.A).left ≫ 𝟙 _) ^ (N : ℤ) *
          h ((1 : 𝟙_ (Over (Sp V)) ⟶ D.P.A).left ≫ ((toUnit D.P.A ≫ b) * 𝟙 D.P.A).left) ^ (-(N : ℤ))) ^ N * _ = _
        rw [comp_transl, Category.comp_id, _root_.mul_one, toUnit_unit, Category.id_comp]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
        module)
    have hx' : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
        val Ψ (1 : T ⟶ D.P.A).left z J ^ N * val κ (toUnit T ≫ b).left z J = gm T.hom z ⊤ x := fun T z J hJ => by
      rw [← hx T (toUnit T) z J hJ, ← Over.comp_left, MonObj.comp_one]
    obtain ⟨z₀⟩ := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J₀, hJ₀⟩ := exists_good' hL z₀
    have e := hx' _ z₀ J₀ hJ₀
    rw [v1 _ z₀ J₀ hJ₀, ← ha z₀ J₀ hJ₀, ← pow_mul, ← sq, ← hgb, hw.2 κ hκ z₀ J₀ hJ₀] at e
    have e' := (congrArg Units.val e).trans (Frames.gm_top_eq x z₀)
    rw [Units.val_one, cst_eq, ← map_one (cstH z₀), ← map_one (algebraMap V (FractionRing V))] at e'
    have e'' := IsFractionRing.injective V (FractionRing V) (cstH_inj z₀ e')
    have hx1 : x = 1 := Units.ext ((Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.injective
      (e''.symm.trans (map_one _).symm))
    rw [hx' T z J hJ, hx1, map_one]
  · have d := Frames.charVal_nsmul g χ hJ N
    rw [hgN, zero_val χ hJ, _root_.one_mul] at d
    rw [vΨ _ _ z J hJ, mul_pow (val (g.s χ) _ z J), ha z J hJ]
    rw [Over.w]
    refine congrArg₂ (· * ·) (Eq.trans (Finset.prod_congr rfl fun i _ => ?_) d) rfl
    rw [Category.comp_id, MonObj.comp_pow, ← Category.assoc, comp_toUnit, ← hgb]
    rfl

theorem exists_vals [IsLocalRing V] {θ : Th D.P} (hθ : GenAll D.P θ) (N : ℕ) (χ : D.X)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D (FractionRing V) χ) (DegPre.famε 1))) {C : Type}
    (g : C → GtPtF D (FractionRing V)) (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A)) (hgb : ∀ c, (g c).b = toUnit _ ≫ b c)
    (w : ∀ c, Frm D (FractionRing V) 1 (g c).b) (Ψ : ∀ c, LB.Gen (psiLB D.P N (b c))) (hΨ : ∀ c, (Ψ c).IsGen)
    (vΨ : ∀ c z J, Good D.P.L z J → val (Ψ c) (toUnit (TF (R := V) (FractionRing V)) ≫ D.c χ).left z J =
      (val ((g c).s χ) (𝟙 _) z J * val (w c) (𝟙 _) z J) ^ N)
    (T : C → V) (hT : ∀ c, IsCoef 1 (g c) (w c) χ s (algebraMap V (FractionRing V) (T c))) :
    ∃ (ρ : LB.Gen (LB.LinComb D.P.L (fun _ : Fin 1 => (D.c χ).left) (fun _ => -1))) (a : C → Γ(Sp V, ⊤)),
      (∀ c c', T c ^ N * (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (a c') =
        T c' ^ N * (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (a c)) ∧
      ∀ c (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
        gs T.hom z ⊤ (a c) = sval θ ((toUnit T ≫ b c) * (toUnit _ ≫ D.c χ)).left z J ^ N *
          (val (Ψ c) (toUnit T ≫ D.c χ).left z J * val ρ T.hom z J ^ N).val := by
  have hL := D.P.isLB
  obtain ⟨ρ, hρ⟩ := exists_gen_local (D := D) (fun _ : Fin 1 => (D.c χ).left) (fun _ => -1)
  have hv : ∀ c, ∃ a : Γ(Sp V, ⊤), ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
      gs T.hom z ⊤ a = sval θ ((toUnit T ≫ b c) * (toUnit _ ≫ D.c χ)).left z J ^ N *
        (val (Ψ c) (toUnit T ≫ D.c χ).left z J * val ρ T.hom z J ^ N).val := fun c => by
    obtain ⟨u, hu, vu⟩ := ((grep_gen (Y := 𝟙_ (Over (Sp V))) (Ψ c) (hΨ c) (D.c χ).left).mul
      ((grep_gen ρ hρ (𝟙 _)).pow N)).out hL (fun _ : Fin 1 => (b c * D.c χ).left) (fun _ => -(N : ℤ)) (fun U _ h => by
        rw [Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one]
        show h ((D.c χ).left ≫ 𝟙 _) ^ (N : ℤ) *
          h ((D.c χ).left ≫ ((toUnit D.P.A ≫ b c) * 𝟙 D.P.A).left) ^ (-(N : ℤ)) * _ = _
        rw [comp_transl, Category.comp_id, Category.id_comp, toUnit_unit, Category.id_comp]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ← natCast_zsmul]
        module)
    obtain ⟨s', hs'⟩ := exists_powSec hL θ (b c * D.c χ).left N u hu (K' := PEmpty) PEmpty.elim PEmpty.elim
      (fun U _ f => by simp)
    obtain ⟨a, ha⟩ := exists_fn s'
    refine ⟨a, fun T z J hJ => ?_⟩
    have e := hs' _ (toUnit T).left z J hJ
    rw [ha, vu T (toUnit T) z J hJ, ← Over.comp_left, MonObj.comp_mul, Category.comp_id] at e
    exact e
  choose a ha using hv
  refine ⟨ρ, a, fun c c' => ?_, ha⟩
  let T₁ : Over (Sp V) := TF (R := V) (FractionRing V)
  let tr : T₁ ⊗ D.P.A ⟶ T₁ ⊗ D.P.A := lift (fst _ _) (snd _ _ * (toUnit _ ≫ D.c χ)⁻¹)
  obtain ⟨u, hu, vu⟩ := ((grep_gen (Y := T₁ ⊗ D.P.A) ρ hρ (toUnit (T₁ ⊗ D.P.A)).left).mul
    (grep_gen (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig D.rig_gen
      (toUnit (T₁ ⊗ D.P.A)).left)).inv.out hL ![(toUnit (T₁ ⊗ D.P.A) ≫ D.c χ).left, (1 : T₁ ⊗ D.P.A ⟶ D.P.A).left] ![1, -1]
      (fun U _ h => by
        rw [Fin.prod_univ_two, Fin.prod_univ_one, Fintype.prod_unique]
        show (h (toUnit (T₁ ⊗ D.P.A) ≫ D.c χ).left ^ (-1 : ℤ) * h (1 : T₁ ⊗ D.P.A ⟶ D.P.A).left ^ (1 : ℤ))⁻¹ = _
        exact (mul_inv _ _).trans (congrArg₂ (· * ·) (by rw [zpow_neg_one, inv_inv]; exact (zpow_one _).symm)
          (by rw [zpow_one]; exact (zpow_neg_one _).symm)))
  obtain ⟨t, ht⟩ := exists_powSec hL s tr.left 1 u hu (fun _ : Fin 1 => (snd T₁ D.P.A).left) (fun _ => 1)
    (fun U _ h => by
      have e₁ : tr.left ≫ DegPre.famφ D (FractionRing V) χ 1 = (snd T₁ D.P.A).left := by
        show (tr ≫ (snd T₁ D.P.A * (toUnit _ ≫ D.c χ))).left = _
        rw [MonObj.comp_mul, lift_snd, ← Category.assoc, comp_toUnit, inv_mul_cancel_right]
      have e₂ : tr.left ≫ DegPre.famφ D (FractionRing V) χ 2 = (toUnit (T₁ ⊗ D.P.A) ≫ D.c χ).left := by
        show (tr ≫ (toUnit _ ≫ D.c χ)).left = _
        rw [← Category.assoc, comp_toUnit]
      have e₃ : tr.left ≫ DegPre.famφ D (FractionRing V) χ 3 = (1 : T₁ ⊗ D.P.A ⟶ D.P.A).left := by
        show (tr ≫ (1 : T₁ ⊗ D.P.A ⟶ D.P.A)).left = _
        rw [MonObj.comp_one]
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_one, e₁, e₂, e₃]
      show (_ ^ (((1 : ℕ) : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ)) ^ 1 *
        (h (toUnit (T₁ ⊗ D.P.A) ≫ D.c χ).left ^ (1 : ℤ) * h (1 : T₁ ⊗ D.P.A ⟶ D.P.A).left ^ (-1 : ℤ)) = _
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_pow]
      module)
  obtain ⟨lam, hlam⟩ := hθ (FractionRing V) T₁.hom t
  obtain ⟨z⟩ := exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have key : ∀ c, cstH z (algebraMap V (FractionRing V) (T c)) ^ N = gs (𝟙 _) z ⊤ lam ^ N *
      cstH z (algebraMap V (FractionRing V) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (a c))) := fun c => by
    have e₀ := hT c z J hJ
    have e₁ := ht _ (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left z J hJ
    have e₂ := hlam _ (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left z J hJ
    have e₃ : gs T₁.hom z ⊤ (a c) = cstH z (algebraMap V (FractionRing V)
        ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (a c))) := by
      rw [← cst_eq]
      exact ((congrArg (fun q => gs q z ⊤ (a c)) (Frames.toUnit_left_eq (V := V))).trans
        (GlobalTheory.RatioVal.gs_specMap _ z _)).trans (GlobalTheory.RatioVal.gs_id_const z _).symm
    have a₁ : (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left ≫ tr.left = (lift (𝟙 T₁) (g c).b).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, MonObj.comp_mul, lift_snd, GrpObj.comp_inv, ← Category.assoc,
        comp_toUnit, mul_inv_cancel_right, hgb]
    have a₂ : (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left ≫ (toUnit (T₁ ⊗ D.P.A)).left = T₁.hom :=
      Over.w _
    have a₃ : (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left ≫ (fst T₁ D.P.A).left = 𝟙 _ := by
      rw [← Over.comp_left, lift_fst]; rfl
    have a₄ : (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left ≫ (snd T₁ D.P.A).left =
        ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ)).left := by rw [← Over.comp_left, lift_snd]
    rw [a₁, vu _ _ z J hJ, a₂, pow_one] at e₁
    have e₄ := e₁.symm.trans (e₂.trans (congrArg₂ (fun q q' => gs q z ⊤ lam * sval θ q' z J) a₃ a₄))
    rw [Units.mul_inv_eq_iff_eq_mul] at e₄
    rw [← e₃, ha c T₁ z J hJ, vΨ c z J hJ, ← mul_pow, Units.val_pow_eq_pow_val, ← mul_pow, ← mul_pow, ← cst_eq]
    congr 1
    rw [pow_one, e₄] at e₀
    refine (Units.mul_left_inj (rigV D T₁.hom z J)).1 (e₀.trans ?_)
    simp only [Units.val_mul, rigV]
    ring
  refine IsFractionRing.injective V (FractionRing V) (cstH_inj z ?_)
  simp only [map_mul, map_pow]
  rw [key, key]
  ring

end Integral

end GlobalTheory.Poinc.Sep.ConjPt
