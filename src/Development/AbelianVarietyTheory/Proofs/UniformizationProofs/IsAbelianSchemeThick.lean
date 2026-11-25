module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GtCoordCompare

section Refine

variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def Refines (M : LB Y) (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ σ : M.ι → K → L.ι, (∀ i, M.U i ≤ LB.wchart L φ (σ i)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : M.ι), r z ∈ M.U i → r z ∈ M.U j →
      gm r z (M.U i ⊓ M.U j) (M.g i j) = trF φ ε r z (σ i) (σ j)

theorem refines_self (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Refines (LB.LinComb L φ ε) L φ ε :=
  ⟨id, fun _ => le_rfl, fun _ r z i j hi hj => gm_linComb L φ ε r z i j hi hj⟩

theorem Refines.linComb {M : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Refines M L φ ε)
    (ψ : K' → (Y' ⟶ Y)) (δ : K' → ℤ) :
    Refines (LB.LinComb M ψ δ) L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1) := by
  obtain ⟨σ, le, hg⟩ := h
  refine ⟨fun j p => σ (j p.1) p.2, fun j y hy => Set.mem_iInter.2 fun p => ?_, fun Z r z i j hi hj => ?_⟩
  · exact Set.mem_iInter.1 (le _ (Set.mem_iInter.1 hy p.1)) p.2
  · refine (gm_linComb M ψ δ r z i j hi hj).trans ?_
    rw [trF, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hg Z (r ≫ ψ a) z _ _ (Set.mem_iInter.1 hi a) (Set.mem_iInter.1 hj a), trF, ← Finset.prod_zpow]
    simp only [zpow_mul, Category.assoc]

theorem isGen_one : (LB.oneGen L (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

end Refine

section

variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)

variable {q a p}

theorem gm_gen {N : LB B} {t : LB.Gen N} (ht : t.IsGen) {Z : Scheme.{0}} (r : Z ⟶ B) (z : Z)
    {j j' : N.ι} (h : r z ∈ N.U j) (h' : r z ∈ N.U j') :
    gm r z _ (t.s j) = gm r z _ (N.g j j') * gm r z _ (t.s j') := by
  have hm : r z ∈ N.U j ⊓ N.U j' := ⟨h, h'⟩
  exact (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _) (ht j j')).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res r z _ hm _))))

end

theorem gm_res_pull_top {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (f : Y ⟶ X) {V : Y.Opens}
    (hz : r z ∈ V) (h : V ≤ f ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)ˣ) :
    gm r z V (res h (pullU f ⊤ c)) = gm (r ≫ f) z ⊤ c :=
  (gm_res r z h hz _).trans (gm_pull r f z ⊤ trivial c)

end GlobalTheory.GtCoordCompare
