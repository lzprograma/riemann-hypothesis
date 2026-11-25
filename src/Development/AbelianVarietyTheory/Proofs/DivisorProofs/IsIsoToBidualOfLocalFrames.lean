module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace Opposite
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.VB
open GlobalTheory.Twist (resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear freeModule)

namespace GlobalTheory.OmegaGlobal

theorem map_bijective_of_isIso_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) (X Y : D) [IsIso (adj.counit.app X)] :
    Function.Bijective (R.map : (X ⟶ Y) → _) := by
  have h : (R.map : (X ⟶ Y) → _) = adj.homEquiv _ _ ∘ fun φ => adj.counit.app X ≫ φ := by
    funext φ
    simp [Adjunction.homEquiv_unit]
  rw [h]
  exact (adj.homEquiv _ _).bijective.comp
    ((asIso (adj.counit.app X)).homFromEquiv (Z := Y)).symm.bijective

section Frames

variable {X : Scheme.{0}} {F : X.Modules}

theorem isQuasicoherent_of_frames (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)),
    x ∈ U ∧ IsFrame e) : F.IsQuasicoherent := by
  choose U n e hx he using h
  refine QCoh.isQuasicoherent_of_restrict F (fun x => (U x).ι)
    (fun x => ⟨x, by simpa using hx x⟩) fun x => ?_
  have := (isVB_freeModule (U x).toScheme (Fin (n x))).isQuasicoherent
  exact QCoh.isQuasicoherent_of_iso ((isFrame_freeFrame _ _).iso
      ((isFrame_restrict_iff (U x).ι _).2 ((he x).res ((U x).ι_image_le ⊤))))

end Frames

variable {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G]

theorem fst_mul (x y : LieG G) : ptMap (TrivSqZeroExt.fstHom O O O) ≫ (x.1 * y.1) =
    toUnit (specO O O) ≫ η[G] := by
  rw [comp_mul, x.2, y.2]
  exact _root_.mul_one (1 : specO O O ⟶ G)

theorem fst_scale (a : O) (x : LieG G) : ptMap (TrivSqZeroExt.fstHom O O O) ≫
    (ptMap (dualScale a) ≫ x.1) = toUnit (specO O O) ≫ η[G] := by
  refine Eq.trans ?_ x.2
  rw [← Category.assoc]
  congr 1
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext y <;> simp [dualScale]

end GlobalTheory.OmegaGlobal
