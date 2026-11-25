module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPullDeg
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory

namespace PsiInPow

open PsiInPull

variable {R : Type} [CommRing R] [IsDomain R]

theorem psiIn_of_gs (D : DegPre R) (χ : D.X) (J : Ideal R)
    (H : ∀ (q : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens), IsAffineOpen V →
      V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q → ∀ z : Spec (CommRingCat.of (FractionRing R)), jK R z ∈ V →
      ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r =
        (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val) :
    D.PsiIn χ J := by
  intro j' V hV hle h'
  obtain ⟨q, rfl⟩ : ∃ q, j' = fun _ => q := ⟨j' PUnit.unit, rfl⟩
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  by_cases hne : ∃ z, jK R z ∈ V
  swap
  · exact ⟨0, Ideal.zero_mem _, fn_ext fun z hz => (hne ⟨z, hz⟩).elim⟩
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r', hr', e'⟩ := H q V hV hle z hz
  refine ⟨r', hr', fn_ext fun y hy => ?_⟩
  obtain rfl : y = z := Subsingleton.elim (α := Spec (CommRingCat.of (FractionRing R))) y z
  exact (gs_pull (𝟙 _) (jK R) y V hz r').trans (e'.trans
    ((gs_res (𝟙 _) y h' hy _).trans (gs_unit _ _ _ (h' hy) _)).symm)

theorem gs_of_psiIn (D : DegPre R) (χ : D.X) (J : Ideal R) (H : D.PsiIn χ J)
    (q : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V)
    (hle : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q) (z : Spec (CommRingCat.of (FractionRing R))) (hz : jK R z ∈ V) :
    ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r =
      (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val := by
  have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => q) :=
    fun y hy => mem_wchart _ _ _ _ (hle hy)
  obtain ⟨r, hrJ, hr⟩ := H (fun _ => q) V hV hle h
  refine ⟨r, hrJ, ?_⟩
  exact (gs_pull (𝟙 _) (jK R) z V hz r).symm.trans ((congrArg (gs (𝟙 _) z _) hr).trans
    ((gs_res (𝟙 _) z h hz _).trans (gs_unit _ _ _ (h hz) _)))

theorem val_psi_zero (D : DegPre R) (hB : D.TauBimult) {y : (TK R).left} {J} (hJ : Good D.P.L y J) :
    val (D.psi 0) (𝟙 _) y J = (val D.rigK (𝟙 _) y J)⁻¹ := by
  have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
  have t := tauK_mul hJ hB 0 0 0
  have z0 : val (D.tau (0 + 0) 0) (𝟙 _) y J = val (D.tau 0 0) (𝟙 _) y J :=
    congrArg (fun a => val (D.tau a 0) (𝟙 _) y J) (add_zero 0)
  rw [z0, cPoint_zero, C.face, _root_.mul_one] at t
  have t0 : val (D.tau 0 0) (𝟙 _) y J = 1 := mul_eq_left.1 t.symm
  have e : val (D.tau 0 0) (𝟙 _) y J = val (D.psi (0 + 0)) (𝟙 _) y J * (val (D.psi 0) (𝟙 _) y J)⁻¹ *
      (val (D.psi 0) (𝟙 _) y J)⁻¹ * (val D.rigK (𝟙 _) y J)⁻¹ :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  rw [t0, add_zero, mul_inv_cancel, _root_.one_mul] at e
  exact (inv_mul_eq_one.1 e.symm)

end PsiInPow

end GlobalTheory
