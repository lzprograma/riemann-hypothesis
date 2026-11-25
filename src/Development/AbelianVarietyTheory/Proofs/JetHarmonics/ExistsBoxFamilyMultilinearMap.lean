module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxLinear

open GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
  {Z : Scheme.{0}}

theorem ext_val {D : DegPre R} {S T : Fam D F k}
    (h : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      sval (S.s α) (𝟙 _) y J = sval (T.s α) (𝟙 _) y J) : S = T := by
  refine fam_ext fun α jj => fn_ext fun y hy => ?_
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  refine (sec_trans (S.s α) (𝟙 _) y hy (hJ.mem _ (𝟙 _))).trans
    (Eq.trans (congrArg _ (h α y J hJ)) (sec_trans (T.s α) (𝟙 _) y hy (hJ.mem _ (𝟙 _))).symm)

theorem sval_add {D : DegPre R} (S T : Fam D F k) (α : D.X) (q : Z ⟶ (DegPre.BF D F).left) (y : Z) {J}
    (hJ : Good D.P.L y J) :
    sval ((S + T).s α) q y J = sval (S.s α) q y J + sval (T.s α) q y J :=
  gs_add q y _ (hJ.mem _ q) _ _

theorem sval_smul {D : DegPre R} (c : F) (S : Fam D F k) (α : D.X) (q : Z ⟶ (DegPre.BF D F).left) (y : Z) {J}
    (hJ : Good D.P.L y J) :
    sval ((c • S).s α) q y J = gs (X := Spec (CommRingCat.of F)) (q ≫ (fst (TF (R := R) F) D.P.A).left) y ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * sval (S.s α) q y J := by
  refine (gs_mul q y _ (hJ.mem _ q) _ _).trans (congrArg (· * _) ?_)
  exact (gs_res q y le_top (hJ.mem _ q) _).trans (gs_pull q (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _)

variable {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem prB_fst (i : Fin j) : prB pD F i ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D'.P.A).left :=
  congrArg (fun g => g.left) (whiskerLeft_fst (TF (R := R) F) (pD.pw.pr i))

theorem box_val {S : Fam D' F k} {s : Fin j → Fam D F k} (h : IsBoxFam pD F k S s) (α' : D'.X)
    (y : (DegPre.BF D' F).left) {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    (∏ a, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F α' a) ^ DegPre.famε k a).val * sval (S.s α') (𝟙 _) y J' =
      ∏ i, sval ((s i).s (pD.xe α' i)) (𝟙 _ ≫ prB pD F i) y J := by
  obtain ⟨hφ, H⟩ := h α'
  exact boxPull_val (w := pD.w) (hφ := hφ) (s := fun i => (s i).s (pD.xe α' i)) H (𝟙 _) y hJ hJ'

theorem prod_update {A S : Type*} [CommMonoid S] {j : ℕ} [DecidableEq (Fin j)] (g : Fin j → A → S) (s : Fin j → A)
    (i : Fin j) (x : A) :
    ∏ l, g l (Function.update s i x l) = g i x * ∏ l ∈ Finset.univ.erase i, g l (s l) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  refine congrArg _ (Finset.prod_congr rfl fun l hl => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

theorem box_unique {S T : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s)
    (hT : IsBoxFam pD F k T s) : S = T :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    exact (Units.mul_right_inj _).1 ((box_val pD hS α y hJ hJ').trans (box_val pD hT α y hJ hJ').symm)

theorem box_add [DecidableEq (Fin j)] {S S₁ S₂ : Fam D' F k} {s : Fin j → Fam D F k} {i : Fin j} {a b : Fam D F k}
    (h : IsBoxFam pD F k S (Function.update s i (a + b))) (h₁ : IsBoxFam pD F k S₁ (Function.update s i a))
    (h₂ : IsBoxFam pD F k S₂ (Function.update s i b)) : S = S₁ + S₂ :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    have p := prod_update (fun l (t : Fam D F k) => sval (t.s (pD.xe α l)) (𝟙 _ ≫ prB pD F l) y J) s i
    have e := (box_val pD h α y hJ hJ').trans (p _)
    have e₁ := (box_val pD h₁ α y hJ hJ').trans (p _)
    have e₂ := (box_val pD h₂ α y hJ hJ').trans (p _)
    refine (Units.mul_right_inj _).1 (e.trans ?_)
    rw [sval_add _ _ _ _ _ hJ, sval_add _ _ _ _ _ hJ', mul_add, add_mul, e₁, e₂]

theorem box_smul [DecidableEq (Fin j)] {S S₁ : Fam D' F k} {s : Fin j → Fam D F k} {i : Fin j} {c : F} {a : Fam D F k}
    (h : IsBoxFam pD F k S (Function.update s i (c • a))) (h₁ : IsBoxFam pD F k S₁ (Function.update s i a)) :
    S = c • S₁ :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    have p := prod_update (fun l (t : Fam D F k) => sval (t.s (pD.xe α l)) (𝟙 _ ≫ prB pD F l) y J) s i
    have e := (box_val pD h α y hJ hJ').trans (p _)
    have e₁ := (box_val pD h₁ α y hJ hJ').trans (p _)
    refine (Units.mul_right_inj _).1 (e.trans ?_)
    rw [sval_smul _ _ _ _ _ hJ, sval_smul _ _ _ _ _ hJ', Category.assoc, prB_fst, mul_left_comm, e₁,
      _root_.mul_assoc]

end GlobalTheory.BoxLinear

namespace GlobalTheory

theorem exists_boxFam_multilinear : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), ∃ bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => Fam D F k) (Fam D' F k), ∀ (s : Fin j → Fam D F k) (S : Fam D' F k), IsBoxFam pD F k S s ↔ S = bx s := by
  intro hG R _ _ j D D' pD F _ _ k
  choose bx hbx using BoxFamily.exists_isBoxFam hG R j D D' pD F k
  refine ⟨⟨bx, fun s i a b => BoxLinear.box_add pD (hbx _) (hbx _) (hbx _),
    fun s i c a => BoxLinear.box_smul pD (hbx _) (hbx _)⟩, fun s S => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact BoxLinear.box_unique pD h (hbx s)
  · rw [h]; exact hbx s

end GlobalTheory
