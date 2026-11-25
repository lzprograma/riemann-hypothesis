module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeThick
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.SeparatedSymmetricModel

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnifPreCompare

section Rigid

variable {X X' T Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem exists_ratio {M : LB X} (cov : ∀ x, ∃ j, x ∈ M.U j) {t t' : LB.Gen M} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : M.ι), r z ∈ M.U j →
      gm r z _ (t.s j) = gm r z ⊤ u * gm r z _ (t'.s j) := by
  obtain ⟨u, hu⟩ := glue_unit ⊤ M.U (fun _ => le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (cov x))
    (fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, GtCoordCompare.gm_gen ht (𝟙 X) x hx.1 hx.2,
        GtCoordCompare.gm_gen ht' (𝟙 X) x hx.1 hx.2, ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div])
  refine ⟨u, fun Z r z j hj => ?_⟩
  rw [← gm_res r z (le_top : M.U j ≤ ⊤) hj u, hu, map_mul, map_inv, inv_mul_cancel_right]

theorem exists_rigidified (hL : L.IsLB) (hL' : L'.IsLB) (π : X' ⟶ T) (σ : T ⟶ X') (hσ : σ ≫ π = 𝟙 T)
    (w₀ : LB.Iso L' (L.pull F)) (hw₀ : w₀.IsGen) (ρ' : LB.Gen (L'.pull σ)) (hρ' : ρ'.IsGen) {φ : Y ⟶ X}
    (ρ : LB.Gen (L.pull φ)) (hρ : ρ.IsGen) (h : T ⟶ Y) (e : σ ≫ F = h ≫ φ) :
    ∃ w : LB.Iso L' (L.pull F), w.IsGen ∧ PMaps w (K := PUnit) (fun _ => σ) (fun _ => φ) (fun _ => 1) ρ' ρ h := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w₀).1 hw₀) hL hL' ρ' hρ'
  have ex : ∀ g : T ⟶ X, g = h ≫ φ → ∃ t' : LB.Gen (L.pull g), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) p,
      r z ∈ (L.pull g).U p → gm r z _ (t'.s p) = gm (r ≫ h) z ((L.pull φ).U p) (ρ.s p) := by
    rintro _ rfl
    exact ⟨LB.pullGen L _ _ ρ h, DVR.pullGen_isGen _ _ _ _ hρ h, fun Z r z p hp =>
      (gm_res r z _ hp _).trans (gm_pull r h z _ (mem_pull.2 (mem_pull₂.1 hp)) _)⟩
  obtain ⟨t', ht', hv'⟩ := ex _ e
  obtain ⟨u, hu⟩ := exists_ratio (M := L.pull (σ ≫ F)) (fun x => by
    obtain ⟨j, hj⟩ := exists_chart hL (F (σ x))
    exact ⟨fun _ => j, mem_pull₂.2 hj⟩) ht' ht
  let w : LB.Iso L' (L.pull F) := ⟨fun p => res le_top (pullU π ⊤ u) * w₀.s p⟩
  have hw : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gw w r z j k = gm (r ≫ π) z ⊤ u * gw w₀ r z j k := fun Z r z j k hj hk =>
    (map_mul _ _ _).trans (congrArg (· * _) (GtCoordCompare.gm_res_pull_top r z π
      (V := (L.pull F).U (fun _ => j) ⊓ L'.U k) ⟨mem_pull.2 hj, hk⟩ _ u))
  refine ⟨w, (isGen_iff w).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z p q hp hq => ?_⟩
  · rw [hw Z r z j k hj hk, hw Z r z j' k' hj' hk', (isGen_iff w₀).1 hw₀ Z r z j j' k k' hj hj' hk hk']
    exact mul_left_comm _ _ _
  · have m : r z ∈ (L.pull (σ ≫ F)).U p := mem_pull₂.2 (hp _)
    refine (hv' Z r z p m).symm.trans ((hu Z r z p m).trans ?_)
    refine (congrArg _ (hv Z r z p q m (Set.mem_iInter.2 hq))).trans ?_
    rw [pw, Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, hw Z (r ≫ σ) z _ _ (hp _) (hq _),
      Category.assoc, hσ, Category.comp_id, _root_.mul_assoc]

end Rigid

end GlobalTheory.UnifPreCompare
