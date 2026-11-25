module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceComplexPointsOfProjVariety
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Formalism.LocalRingCardinality.DataDIV
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.Tactic.PNatToNat

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff, Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceComplexPointsOfProjVariety\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint\npublic import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.InnerProductSpace.Calculus\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.TypeStar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open MeasureTheory
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.CxPts
open scoped ContDiff

namespace GlobalTheory.ProjVar.Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ Δ' : Y.Dv} {g g' : Y.Fnˣ}
  {y : Y.pts σ} {f f' : Y.FnC σ}

theorem exists_mem_ptsIn {U : Y.X.Opens} (h : genericPoint Y.X ∈ U) :
    ∃ y : Y.pts σ, y ∈ ptsIn Y.str σ U :=
  have := ComplexPoints.surjective_specMap_field σ
  have : Smooth Y.str := SmoothOfRelativeDimension.smooth Y.dim _
  have ⟨x, hx, hU⟩ := ComplexPoints.exists_geomPoint_mem Y.str (Spec.map (CommRingCat.ofHom σ))
    U.isOpen.isLocallyClosed ⟨_, h⟩
  ⟨⟨x, hx⟩, mem_ptsIn_iff.2 (hU _)⟩

instance nonempty_pts : Nonempty (Y.pts σ) := ⟨(exists_mem_ptsIn (U := ⊤) trivial).choose⟩

theorem val_cx (a : Y.Fn) (y : Y.pts σ) : val y (Y.cx σ a) = ratVal a y := by
  by_cases h : RegAt (base y) a
  · obtain ⟨U, hU, a, rfl⟩ := h.exists_fnOf
    rw [val_cx_fnOf hU, ratVal_fnOf (mem_ptsIn_iff.2 hU)]
  · rw [val_of_not_regC (mt regC_cx_iff.1 h)]; rw [ratVal, dite_eq_right (show ¬ RegAt (under y) a from h)]


variable (σ) in
def eqnSet (Δ : Y.Dv) (g : Y.Fnˣ) : Set (Y.pts σ) := {y | Δ.IsEqn (base y) g}

def eqn (Δ : Y.Dv) (y : Y.pts σ) : Y.Fnˣ := (Δ.exists_isEqn (base y)).choose

theorem mem_eqnSet (Δ : Y.Dv) (y : Y.pts σ) : y ∈ eqnSet σ Δ (eqn Δ y) :=
  (Δ.exists_isEqn (base y)).choose_spec

def fval (g : Y.Fnˣ) (f : Y.FnC σ) (y : Y.pts σ) : ℂ := val y (f * Y.cx σ g)

def tv (g g' : Y.Fnˣ) (y : Y.pts σ) : ℂ := val y (Y.cx σ (g' / g))

theorem fval_cx (a : Y.Fn) (y : Y.pts σ) : fval g (Y.cx σ a) y = ratVal (a * (g : Y.Fn)) y := by
  rw [fval, ← map_mul, val_cx]

theorem tv_ne_zero (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') : tv g g' y ≠ 0 :=
  val_cx_ne_zero_iff.2 ((IsEqn.iff_unitAt h).1 h')

theorem mul_cx_eq (f : Y.FnC σ) (g g' : Y.Fnˣ) :
    f * Y.cx σ g' = Y.cx σ (g' / g) * (f * Y.cx σ g) := by
  rw [mul_left_comm, ← map_mul, div_mul_cancel₀ _ g.ne_zero]

theorem fval_trans (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') (f : Y.FnC σ) :
    fval g' f y = tv g g' y * fval g f y := by
  rw [fval, mul_cx_eq f g g', val_unit_mul (tv_ne_zero h h')]; rfl

theorem tv_mul_mul {g₁ g₁' : Y.Fnˣ} (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') :
    tv (g * g₁) (g' * g₁') y = tv g g' y * tv g₁ g₁' y := by
  rw [tv, Units.val_mul, Units.val_mul, mul_div_mul_comm, map_mul, val_unit_mul (tv_ne_zero h h')]
  rfl

theorem tv_mul {g'' : Y.Fnˣ} (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') :
    tv g g' y * tv g' g'' y = tv g g'' y := by
  rw [← tv_mul_mul h h', tv, tv, Units.val_mul, Units.val_mul, mul_comm (g : Y.Fn),
    mul_div_mul_left _ _ g'.ne_zero]

theorem tv_pow (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') (k : ℕ) :
    tv (g ^ k) (g' ^ k) y = tv g g' y ^ k := by
  rw [tv, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← div_pow, map_pow]
  exact ((regC_of_val_ne_zero (tv_ne_zero h h')).hasVal.pow k).val_eq

def SecReg (Δ : Y.Dv) (f : Y.FnC σ) (y : Y.pts σ) : Prop :=
  ∃ g, y ∈ eqnSet σ Δ g ∧ RegC y (f * Y.cx σ g)

def SecZero (Δ : Y.Dv) (f : Y.FnC σ) (y : Y.pts σ) : Prop :=
  ∃ g, y ∈ eqnSet σ Δ g ∧ HasVal y (f * Y.cx σ g) 0

theorem secReg_iff (h : y ∈ eqnSet σ Δ g) : SecReg Δ f y ↔ RegC y (f * Y.cx σ g) :=
  ⟨fun ⟨g', h', hf⟩ => mul_cx_eq f g' g ▸ (regC_mul_iff (tv_ne_zero h' h)).2 hf, fun hf => ⟨g, h, hf⟩⟩

theorem secReg_cx_iff {a : Y.Fn} : SecReg Δ (Y.cx σ a) y ↔ Δ.RegularAt (base y) a :=
  exists_congr fun _ => and_congr_right fun _ => by rw [← map_mul, regC_cx_iff]

theorem secReg_cx_of_mem {a : Y.Fn} (h : a ∈ Y.H0 Δ) (y : Y.pts σ) : SecReg Δ (Y.cx σ a) y :=
  secReg_cx_iff.2 (mem_riemannRochSpace_iff_regularAt_everywhere.1 h _)

theorem hasVal_sum_smul {ι : Type*} [Fintype ι] {e : ι → Y.FnC σ} (h : y ∈ eqnSet σ Δ g)
    (he : ∀ i, SecReg Δ (e i) y) (c : ι → ℂ) :
    HasVal y ((∑ i, c i • e i) * Y.cx σ g) (∑ i, c i * fval g (e i) y) := by
  rw [Finset.sum_mul]
  exact HasVal.sum fun i _ => smul_mul_assoc (c i) (e i) _ ▸ ((secReg_iff h).1 (he i)).hasVal.smul _

theorem fval_mul (hg : y ∈ eqnSet σ Δ g) (hg' : y ∈ eqnSet σ Δ' g') (h : SecReg Δ f y)
    (h' : SecReg Δ' f' y) : fval (g * g') (f * f') y = fval g f y * fval g' f' y := by
  rw [fval, Units.val_mul, map_mul, mul_mul_mul_comm,
    val_mul ((secReg_iff hg).1 h) ((secReg_iff hg').1 h')]
  rfl

theorem fval_pow (hg : y ∈ eqnSet σ Δ g) (h : SecReg Δ f y) (k : ℕ) :
    fval (g ^ k) (f ^ k) y = fval g f y ^ k := by
  rw [fval, Units.val_pow_eq_pow_val, map_pow, ← mul_pow]
  exact (((secReg_iff hg).1 h).hasVal.pow k).val_eq


variable (Y σ) in
structure Met (Δ : Y.Dv) where

  h : Y.Fnˣ → Y.pts σ → ℝ

  nonneg : ∀ g y, 0 ≤ h g y

  trans : ∀ g g' y, y ∈ eqnSet σ Δ g → y ∈ eqnSet σ Δ g' → h g y = ‖tv g g' y‖ ^ 2 * h g' y

namespace Met

variable (m : Met Y σ Δ) (m' : Met Y σ Δ')

def wt (g : Y.Fnˣ) (y : Y.pts σ) : ℝ := -Real.log (m.h g y)

def posSet : Set (Y.pts σ) := {y | 0 < m.h (eqn Δ y) y}


section Cover

variable {ι : Type} (S : ι → Set (Y.pts σ)) (e : ι → Y.Fnˣ) (sub : ∀ i, S i ⊆ eqnSet σ Δ (e i))
  (cover : ∀ y, ∃ i, y ∈ S i) (w : ι → Y.pts σ → ℝ) (hw : ∀ i y, 0 ≤ w i y)
  (compat : ∀ i j y, y ∈ S i → y ∈ S j → w i y = ‖tv (e i) (e j) y‖ ^ 2 * w j y)

def ofCover : Met Y σ Δ where
  h g y := ‖tv g (e (cover y).choose) y‖ ^ 2 * w (cover y).choose y
  nonneg _ _ := mul_nonneg (sq_nonneg _) (hw _ _)
  trans g g' y hg hg' := by rw [← mul_assoc, ← mul_pow, ← norm_mul, tv_mul hg hg']


include sub compat in
theorem ofCover_h {i : ι} (hi : y ∈ S i) : (ofCover (Δ := Δ) S e cover w hw).h (e i) y = w i y :=
  (compat i _ y hi (cover y).choose_spec).symm

end Cover


variable {m} in
def SmoothOn (m : Met Y σ Δ) (S : Set (Y.pts σ)) : Prop :=
  S ⊆ m.posSet ∧ ∀ g, (Y.an σ).SmoothOn (S ∩ eqnSet σ Δ g) (m.wt g)


end Met

open Met

theorem cover_pair (Δ Δ' : Y.Dv) (y : Y.pts σ) :
    ∃ i : Y.Fnˣ × Y.Fnˣ, y ∈ eqnSet σ Δ i.1 ∩ eqnSet σ Δ' i.2 :=
  ⟨(_, _), mem_eqnSet Δ y, mem_eqnSet Δ' y⟩


variable (Y σ Δ Δ') in
def mAdd (m : Met Y σ Δ) (m' : Met Y σ Δ') : Met Y σ (Δ + Δ') :=
  ofCover _ (fun i => i.1 * i.2) (cover_pair Δ Δ') (fun i y => m.h i.1 y * m'.h i.2 y)
    fun _ _ => mul_nonneg (m.nonneg _ _) (m'.nonneg _ _)


variable (Y σ Δ) in
def mPow (k : ℕ) (m : Met Y σ Δ) : Met Y σ (k • Δ) :=
  ofCover _ (· ^ k) (fun y => ⟨_, mem_eqnSet Δ y⟩) (fun g y => m.h g y ^ k)
    fun _ _ => pow_nonneg (m.nonneg _ _) _


open Classical in
variable (Y σ Δ) in
def fsMet {κ : Type} [Fintype κ] (e : κ → Y.FnC σ) : Met Y σ Δ where
  h g y := if ∀ k, SecReg Δ (e k) y then (∑ k, ‖fval g (e k) y‖ ^ 2)⁻¹ else 0
  nonneg g y := by split_ifs <;> positivity
  trans g g' y hg hg' := by
    have := tv_ne_zero hg hg'
    split_ifs
    · simp only [fval_trans hg hg', norm_mul, mul_pow, ← Finset.mul_sum, mul_inv]
      rw [mul_inv_cancel_left₀ (by positivity)]
    · rw [mul_zero]

section OfWeight

variable {L : LB Y.X} {r : L.ι → Y.Fnˣ}

theorem tv_eq_gv (hp : Presents Δ L r) {i j : L.ι} (hi : y ∈ ptsIn Y.str σ (L.U i))
    (hj : y ∈ ptsIn Y.str σ (L.U j)) : tv (r j) (r i) y = gv Y.str σ L i j y := by
  have h : base y ∈ L.U i ⊓ L.U j := ⟨mem_ptsIn_iff.1 hi, mem_ptsIn_iff.1 hj⟩
  rw [tv, hp.isRatSec i j (gen_mem h), mul_div_cancel_right₀ _ (r j).ne_zero, val_cx_fnOf h]
  rfl

theorem ptsIn_subset_eqnSet (hp : Presents Δ L r) (i : L.ι) :
    ptsIn Y.str σ (L.U i) ⊆ eqnSet σ Δ (r i) := fun _ h => hp.isEqn i _ (mem_ptsIn_iff.1 h)


variable (Y σ Δ L r) in
def ofWeight (_ : Presents Δ L r) (φ : Weight Y.str σ L) : Met Y σ Δ :=
  ofCover (fun i => ptsIn Y.str σ (L.U i)) r (fun y => ⟨_, mem_pick φ.isLB y⟩)
    (fun i y => Real.exp (-φ.φ i y)) fun _ _ => (Real.exp_pos _).le

theorem ofWeight_h (hp : Presents Δ L r) (φ : Weight Y.str σ L) {i : L.ι}
    (hi : y ∈ ptsIn Y.str σ (L.U i)) :
    (ofWeight Y σ Δ L r hp φ).h (r i) y = Real.exp (-φ.φ i y) :=
  ofCover_h _ _ (ptsIn_subset_eqnSet hp) _ _ _ (fun i j y hi hj => by
    have := normSq_mul_exp (gv_ne_zero hj hi) 1 (φ.φ i y)
    rw [φ.trans j i y hj hi, sub_add_cancel, mul_one, norm_one, one_pow, one_mul] at this
    rw [tv_eq_gv hp hj hi, φ.trans j i y hj hi, this]) hi

end OfWeight

variable {m : Met Y σ Δ} {m' : Met Y σ Δ'}

theorem mAdd_h (hg : y ∈ eqnSet σ Δ g) (hg' : y ∈ eqnSet σ Δ' g') :
    (mAdd Y σ Δ Δ' m m').h (g * g') y = m.h g y * m'.h g' y :=
  ofCover_h (Δ := Δ + Δ') _ (fun i : Y.Fnˣ × Y.Fnˣ => i.1 * i.2) (fun _ _ (h : _ ∈ eqnSet σ Δ _ ∩ eqnSet σ Δ' _) => IsEqn.add h.1 h.2) _ _ _
    (fun i j y hi hj => by
      rw [m.trans _ _ y hi.1 hj.1, m'.trans _ _ y hi.2 hj.2, tv_mul_mul hi.1 hj.1, norm_mul]; ring)
    (i := (g, g')) ⟨hg, hg'⟩

theorem mPow_h (hg : y ∈ eqnSet σ Δ g) (k : ℕ) : (mPow Y σ Δ k m).h (g ^ k) y = m.h g y ^ k :=
  ofCover_h (Δ := k • Δ) _ (· ^ k) (fun _ _ h => IsEqn.nsmul h k) _ _ _
    (fun i j y hi hj => by rw [m.trans _ _ y hi hj, tv_pow hi hj, norm_pow]; ring) hg

theorem fsMet_h {κ : Type} [Fintype κ] {e : κ → Y.FnC σ} (he : ∀ k, SecReg Δ (e k) y) (g : Y.Fnˣ) :
    (fsMet Y σ Δ e).h g y = (∑ k, ‖fval g (e k) y‖ ^ 2)⁻¹ := ite_eq_left he


variable (Y σ Δ) in
def pn (m : Met Y σ Δ) (f : Y.FnC σ) (y : Y.pts σ) : ℝ :=
  ‖fval (eqn Δ y) f y‖ ^ 2 * m.h (eqn Δ y) y


variable (Y σ Δ) in
def pnK (m : Met Y σ Δ) (f : Y.FnC σ) (y : Y.pts σ) : ℝ := pn Y σ Δ m f y

theorem pn_eq (hg : y ∈ eqnSet σ Δ g) : pn Y σ Δ m f y = ‖fval g f y‖ ^ 2 * m.h g y := by
  rw [pn, fval_trans hg (mem_eqnSet Δ y), m.trans g _ y hg (mem_eqnSet Δ y), norm_mul]; ring

theorem pn_mul {a : Y.FnC σ} (ha : RegC y a) (hf : SecReg Δ f y) :
    pn Y σ Δ m (a * f) y = ‖val y a‖ ^ 2 * pn Y σ Δ m f y := by
  rw [pn, pn, fval, mul_assoc, val_mul ha ((secReg_iff (mem_eqnSet Δ y)).1 hf), norm_mul, fval]
  ring

theorem pn_mAdd (hf : SecReg Δ f y) (hf' : SecReg Δ' f' y) :
    pn Y σ _ (mAdd Y σ Δ Δ' m m') (f * f') y = pn Y σ Δ m f y * pn Y σ Δ' m' f' y := by
  have h := mem_eqnSet Δ y
  have h' := mem_eqnSet Δ' y
  rw [pn_eq (IsEqn.add h h'), mAdd_h h h', fval_mul h h' hf hf', pn, pn, norm_mul]; ring

theorem pn_mPow (hf : SecReg Δ f y) (k : ℕ) :
    pn Y σ _ (mPow Y σ Δ k m) (f ^ k) y = pn Y σ Δ m f y ^ k := by
  have h := mem_eqnSet Δ y
  rw [pn_eq (IsEqn.nsmul h k), mPow_h h, fval_pow h hf, pn, norm_pow]; ring

theorem pn_fsMet {κ : Type} [Fintype κ] {e : κ → Y.FnC σ} (he : ∀ k, SecReg Δ (e k) y)
    (hg : y ∈ eqnSet σ Δ g) :
    pn Y σ Δ (fsMet Y σ Δ e) f y = ‖fval g f y‖ ^ 2 / ∑ k, ‖fval g (e k) y‖ ^ 2 := by
  rw [pn_eq hg, fsMet_h he, div_eq_mul_inv]

theorem pn_ofWeight {L : LB Y.X} {r : L.ι → Y.Fnˣ} (hp : Presents Δ L r) (φ : Weight Y.str σ L)
    {i : L.ι} (hi : y ∈ ptsIn Y.str σ (L.U i)) : pn Y σ Δ (ofWeight Y σ Δ L r hp φ) f y =
      ‖fval (r i) f y‖ ^ 2 * Real.exp (-φ.φ i y) := by
  rw [pn_eq (ptsIn_subset_eqnSet hp i hi), ofWeight_h hp φ hi]


variable (Y σ Δ) in
def mSmooth (m : Met Y σ Δ) : Prop := m.SmoothOn univ

def omegaCoeff (c : AlgChart Y.str σ Y.dim) : Y.Fnˣ :=
  frameRat (CanonLB.all Y.str Y.dim).bundle (baseChart _ _) (gen_mem_baseOpen _ _) ⟨c.U, _, c.isFrame⟩


variable (Y σ) in
def vol : Measure (Y.pts σ) :=
  (Y.an σ).topMeasure (CanonLB.all Y.str Y.dim) (Weight.ofFun fun _ => 0) fun a =>
    fval (frameRat _ (baseChart _ _) (gen_mem_baseOpen _ _) a.1) 1

def _root_.GlobalTheory.ProjVar.PosCurrent {D : ℕ} (O : Set (V D)) (u : V D → ℝ) : Prop :=
  LocallyIntegrableOn u O ∧ ∀ χ : V D → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
    (∀ v, 0 ≤ χ v) → ∀ ξ, 0 ≤ ∫ v, u v * (leviV D (fun w => (χ w : ℂ)) v ξ).re

def chartDom (c : AlgChart Y.str σ Y.dim) (Δ : Y.Dv) (g : Y.Fnˣ) : Set (V Y.dim) :=
  c.e.target ∩ c.e.symm ⁻¹' eqnSet σ Δ g


variable (Y σ Δ) in
def mPsh (m : Met Y σ Δ) (ψ : Y.pts σ → ℝ) : Prop :=
  ∀ (c : AlgChart Y.str σ Y.dim) (g : Y.Fnˣ),
    (∀ᵐ v, v ∈ chartDom c Δ g → c.e.symm v ∈ m.posSet) ∧
      PosCurrent (chartDom c Δ g) fun v => m.wt g (c.e.symm v) + ψ (c.e.symm v)

def jac (c : AlgChart Y.str σ Y.dim) (g : Y.Fnˣ) (s : Fin Y.dim → Y.FnC σ) (y : Y.pts σ) : ℂ :=
  (fderiv ℂ (fun v => (WithLp.toLp 2 fun i => fval g (s i) (c.e.symm v) : V Y.dim)) (c.e y)).det

def chartAt (y : Y.pts σ) : AlgChart Y.str σ Y.dim := (AlgChart.exists_mem_source y).choose

variable {s : Fin Y.dim → Y.FnC σ} {c c' : AlgChart Y.str σ Y.dim}


variable (Y σ Δ) in
def redZero (s : Fin Y.dim → Y.FnC σ) (S : Set (Y.pts σ)) : Prop :=
  (∀ i y, SecReg Δ (s i) y) ∧ S = {y | ∀ i, SecZero Δ (s i) y} ∧
    ∀ y ∈ S, jac (chartAt y) (eqn Δ y) s y ≠ 0


variable (Y σ Δ) in
def regOn (G : Y.FnC σ) (S : Set (Y.pts σ)) : Prop := ∀ y ∈ S, SecReg (Y.KY + Δ) G y


variable (Y σ Δ) in
def agreeOn (G G' : Y.FnC σ) (S : Set (Y.pts σ)) : Prop := ∀ y ∈ S, SecZero (Y.KY + Δ) (G - G') y


variable (Y σ Δ) in
def resNorm (m : Met Y σ Δ) (Δ' : Y.Dv) (m' : Met Y σ Δ') (s : Fin Y.dim → Y.FnC σ) (G : Y.FnC σ)
    (y : Y.pts σ) : ℝ :=
  ‖fval (omegaCoeff (chartAt y) * eqn Δ y) G y‖ ^ 2 * m.h (eqn Δ y) y /
    (‖jac (chartAt y) (eqn Δ' y) s y‖ ^ 2 * m'.h (eqn Δ' y) y ^ Y.dim)

end GlobalTheory.ProjVar.Var

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers", "h": "module\n\npublic import Formalism.LocalRingCardinality.DataDIV\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef\npublic import Mathlib.NumberTheory.NumberField.Completion.FinitePlace\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.KrullDimension.Polynomial\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.PNatToNat\nimport Mathlib.Tactic.Polynomial.Basic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter MeasureTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

variable {F : Type} [Field F] [NumberField F]

abbrev Pts (Y : Var F) (σ : F →+* ℂ) : Type := CxPts Y.str σ

structure CxSt (F : Type) [Field F] [NumberField F] : Type 1 where

  [ptsMeas : ∀ (Y : Var F) σ, MeasurableSpace (Pts Y σ)]

  borel : ∀ (Y : Var F) σ, BorelSpace (Pts Y σ)

  vol : ∀ (Y : Var F) σ, Measure (Pts Y σ)

  FnC : Var F → (F →+* ℂ) → Type

  [fnCRing : ∀ Y σ, CommRing (FnC Y σ)]

  [fnCAlg : ∀ Y σ, Algebra ℂ (FnC Y σ)]

  cx : ∀ Y σ, Y.Fn →+* FnC Y σ

  cx_smul : ∀ Y σ (a : F) (f : Y.Fn), cx Y σ (a • f) = σ a • cx Y σ f

  Met : ∀ Y : Var F, (F →+* ℂ) → Y.Dv → Type

  mAdd : ∀ Y σ Δ Δ', Met Y σ Δ → Met Y σ Δ' → Met Y σ (Δ + Δ')

  mPow : ∀ Y σ Δ (k : ℕ), Met Y σ Δ → Met Y σ (k • Δ)

  fsMet : ∀ Y σ Δ {k : Type} [Fintype k], (k → FnC Y σ) → Met Y σ Δ

  pn : ∀ Y σ Δ, Met Y σ Δ → FnC Y σ → Pts Y σ → ℝ

  pnK : ∀ Y σ Δ, Met Y σ Δ → FnC Y σ → Pts Y σ → ℝ

  mSmooth : ∀ Y σ Δ, Met Y σ Δ → Prop

  mPsh : ∀ Y σ Δ, Met Y σ Δ → (Pts Y σ → ℝ) → Prop

  redZero : ∀ (Y : Var F) σ, Y.Dv → (Fin Y.dim → FnC Y σ) → Set (Pts Y σ) → Prop

  agreeOn : ∀ (Y : Var F) σ, Y.Dv → FnC Y σ → FnC Y σ → Set (Pts Y σ) → Prop

  resNorm : ∀ Y σ Δ, Met Y σ Δ → ∀ Δs, Met Y σ Δs → (Fin Y.dim → FnC Y σ) → FnC Y σ → Pts Y σ → ℝ

  regOn : ∀ (Y : Var F) σ, Y.Dv → FnC Y σ → Set (Pts Y σ) → Prop

  ofWeight : ∀ (Y : Var F) σ (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), Presents Δ L r → Weight Y.str σ L → Met Y σ Δ

  pn_ofWeight : ∀ (Y : Var F) σ (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (h : Presents Δ L r) (φ : Weight Y.str σ L)
    (f : Y.Fn) (y : Pts Y σ) (i : L.ι), under y ∈ L.U i → Δ.RegularAt (under y) f →
      pn Y σ Δ (ofWeight Y σ Δ L r h φ) (cx Y σ f) y = ‖ratVal (f * (r i : Y.Fn)) y‖ ^ 2 * Real.exp (-φ.φ i y)

  pn_mAdd : ∀ (Y : Var F) σ (Δ Δ' : Y.Dv) (m : Met Y σ Δ) (m' : Met Y σ Δ') (f f' : Y.Fn) (y : Pts Y σ),
    Δ.RegularAt (under y) f → Δ'.RegularAt (under y) f' →
      pn Y σ _ (mAdd Y σ Δ Δ' m m') (cx Y σ (f * f')) y = pn Y σ Δ m (cx Y σ f) y * pn Y σ Δ' m' (cx Y σ f') y

  pn_mPow : ∀ (Y : Var F) σ (Δ : Y.Dv) (k : ℕ) (m : Met Y σ Δ) (f : Y.Fn) (y : Pts Y σ), Δ.GeneratesAt (under y) f →
      pn Y σ _ (mPow Y σ Δ k m) (cx Y σ (f ^ k)) y = pn Y σ Δ m (cx Y σ f) y ^ k

  pn_mul : ∀ (Y : Var F) σ (Δ : Y.Dv) (m : Met Y σ Δ) (a f : Y.Fn) (y : Pts Y σ), RegAt (under y) a →
    Δ.RegularAt (under y) f → pn Y σ Δ m (cx Y σ (a * f)) y = ‖ratVal a y‖ ^ 2 * pn Y σ Δ m (cx Y σ f) y

  pn_fs : ∀ (Y : Var F) σ (Δ : Y.Dv) {ι κ : Type} [Fintype ι] [Fintype κ] (b : ι → Y.Fn) (X : ι → κ → ℂ) (f : Y.Fn)
    (y : Pts Y σ) (g : Y.Fnˣ), Δ.IsEqn (under y) g → (∀ i, b i ∈ Y.H0 Δ) → Δ.RegularAt (under y) f →
    (∑ k, ‖∑ i, X i k * ratVal (b i * (g : Y.Fn)) y‖ ^ 2) ≠ 0 →
      pn Y σ Δ (fsMet Y σ Δ fun k => ∑ i, X i k • cx Y σ (b i)) (cx Y σ f) y =
        ‖ratVal (f * (g : Y.Fn)) y‖ ^ 2 / ∑ k, ‖∑ i, X i k * ratVal (b i * (g : Y.Fn)) y‖ ^ 2

  vol_eq : HEq vol fun (Y : Var F) σ => Var.vol Y σ := by rfl

  fnC_eq : FnC = fun (Y : Var F) σ => Var.FnC Y σ := by rfl

  fnCRing_eq : HEq fnCRing fun (Y : Var F) σ => (inferInstance : CommRing (Var.FnC Y σ)) := by rfl

  fnCAlg_eq : HEq fnCAlg fun (Y : Var F) σ => (inferInstance : Algebra ℂ (Var.FnC Y σ)) := by rfl

  cx_eq : HEq cx fun (Y : Var F) σ => Var.cx Y σ := by rfl

  met_eq : Met = fun (Y : Var F) σ Δ => Var.Met Y σ Δ := by rfl

  mAdd_eq : HEq mAdd fun (Y : Var F) σ Δ Δ' => Var.mAdd Y σ Δ Δ' := by rfl

  mPow_eq : HEq mPow fun (Y : Var F) σ Δ => Var.mPow Y σ Δ := by rfl

  fsMet_eq : HEq @fsMet fun (Y : Var F) σ Δ => @Var.fsMet F _ Y σ Δ := by rfl

  pn_eq : HEq pn fun (Y : Var F) σ Δ => Var.pn Y σ Δ := by rfl

  pnK_eq : HEq pnK fun (Y : Var F) σ Δ => Var.pnK Y σ Δ := by rfl

  mSmooth_eq : HEq mSmooth fun (Y : Var F) σ Δ => Var.mSmooth Y σ Δ := by rfl

  mPsh_eq : HEq mPsh fun (Y : Var F) σ Δ => Var.mPsh Y σ Δ := by rfl

  redZero_eq : HEq redZero fun (Y : Var F) σ Δ => Var.redZero Y σ Δ := by rfl

  agreeOn_eq : HEq agreeOn fun (Y : Var F) σ Δ => Var.agreeOn Y σ Δ := by rfl

  resNorm_eq : HEq resNorm fun (Y : Var F) σ Δ => Var.resNorm Y σ Δ := by rfl

  regOn_eq : HEq regOn fun (Y : Var F) σ Δ => Var.regOn Y σ Δ := by rfl

  ofWeight_eq : HEq ofWeight fun (Y : Var F) σ Δ L r => Var.ofWeight Y σ Δ L r := by rfl

attribute [instance] CxSt.fnCRing CxSt.fnCAlg

abbrev below {K : Type} [Field K] {Z : Scheme.{0}} (y : Sp K ⟶ Z) : Z := y (IsLocalRing.closedPoint K)


open Classical in
def valAt {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (f : Z.functionField) : K :=
  if h : RegAt (below y) f then (Scheme.stalkClosedPointTo y).hom h.choose else 0

def eqn {Z : Scheme.{0}} [IsIntegral Z] (Δ : CartierDiv Z) (x : Z) : Z.functionFieldˣ := (Δ.exists_isEqn x).choose

structure Ext (v : HeightOneSpectrum (𝓞 F)) : Type where

  w : AbsoluteValue (AlgebraicClosure F) ℝ

  w_alg : ∀ a : F, w (algebraMap F _ a) = NumberField.HeightOneSpectrum.adicAbv F v a

  O : ValuationSubring (AlgebraicClosure F)

  mem_O : ∀ x, x ∈ O ↔ w x ≤ 1

instance Ext.instNonempty (v : HeightOneSpectrum (𝓞 F)) : Nonempty (Ext v) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let K := v.adicCompletion F
  have h1 : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ < 1 := (FinitePlace.norm_lt_one_iff_mem F v a).2 ha
  have h0 : FinitePlace.embedding v (algebraMap (𝓞 F) F a) ≠ 0 := by
    simpa using ha0
  letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne ⟨_, h0, h1.ne⟩
  let L := AlgebraicClosure K
  letI : Algebra F L := ((algebraMap K L).comp (FinitePlace.embedding v)).toAlgebra
  let j : AlgebraicClosure F →ₐ[F] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let N := spectralMulAlgNorm K L
  let w : AbsoluteValue (AlgebraicClosure F) ℝ :=
    (MulRingNorm.mulRingNormEquivAbsoluteValue N.toMulRingNorm).comp (f := j.toRingHom) j.injective
  have hw (x) : w x = spectralNorm K L (j x) := rfl
  have hn (x y) : w (x + y) ≤ max (w x) (w y) := by
    rw [hw, hw, hw, map_add (f := _)]; exact isNonarchimedean_spectralNorm _ _
  refine ⟨⟨w, fun x => ?_, ⟨⟨⟨⟨⟨{x | w x ≤ 1}, ?_⟩, by simp⟩, ?_, by simp⟩, ?_⟩, ?_⟩, fun _ => Iff.rfl⟩⟩
  · rw [hw, j.commutes, ← FinitePlace.norm_embedding]
    exact spectralNorm_extends _
  · intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul] at *
    exact mul_le_one₀ hx (w.nonneg _) hy
  · intro x y hx hy
    exact (hn x y).trans (max_le hx hy)
  · intro x hx
    simpa using hx
  · intro x
    rcases le_total (w x) 1 with h | h
    · exact .inl h
    · refine .inr ?_
      change w x⁻¹ ≤ 1
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ h

def AlgPt (Y : Var F) : Type :=
  {y : Sp (AlgebraicClosure F) ⟶ Y.X // y ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F))}

structure Adl (C : CxSt F) (Y : Var F) : Type where

  D : Y.Dv

  n : ℕ+

  m : ∀ σ, C.Met Y σ D

  ci : InfinitePlace F → ℝ

  lg : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ

structure Model (Y : Var F) : Type 1 where

  X : Scheme.{0}

  p : X ⟶ Sp (𝓞 F)

  ar : IsArithVar p Y.dim

  j : Y.X ⟶ X

  pb : IsPullback j Y.str p (spMap (algebraMap (𝓞 F) F))

namespace Adl

variable {C : CxSt F} {Y : Var F} (A : Adl C Y)

def twist (ci : InfinitePlace F → ℝ) (cf : HeightOneSpectrum (𝓞 F) → ℝ) : Adl C Y :=
  { A with ci := A.ci + ci, lg := fun v e y => A.lg v e y - (A.n : ℕ) * cf v }

def deg : ℝ := (Y.inter (fun _ => A.D) : ℝ) / ((A.n : ℕ) : ℝ) ^ Y.dim

def secs (τ : ℕ) : Set Y.Fn := {f | f ^ (A.n : ℕ) ∈ Y.H0 (τ • A.D)}

def nrmInf (σ : F →+* ℂ) (τ : ℕ) (f : Y.Fn) (y : Pts Y σ) : ℝ :=
  Real.exp (-((τ : ℝ) * A.ci (InfinitePlace.mk σ))) *
    C.pn Y σ (τ • A.D) (C.mPow Y σ A.D τ (A.m σ)) (C.cx Y σ (f ^ (A.n : ℕ))) y ^ (1 / (2 * ((A.n : ℕ) : ℝ)))

def nrmFin (v : HeightOneSpectrum (𝓞 F)) (τ : ℕ) (f : Y.Fn) (e : Ext v) (y : AlgPt Y) : ℝ :=
  e.w (valAt y.1 (f ^ (A.n : ℕ) * (eqn A.D (below y.1) : Y.Fn) ^ τ)) ^ (1 / ((A.n : ℕ) : ℝ)) *
    Real.exp ((τ : ℝ) * A.lg v e y / ((A.n : ℕ) : ℝ))

def supInf (v : InfinitePlace F) (τ : ℕ) (f : Y.Fn) : ℝ := ⨆ y, A.nrmInf v.embedding τ f y

def supFin (v : HeightOneSpectrum (𝓞 F)) (τ : ℕ) (f : Y.Fn) : ℝ :=
  ⨆ q : Ext v × AlgPt Y, A.nrmFin v τ f q.1 q.2

def small (τ : ℕ) : Set Y.Fn :=
  {f | f ∈ A.secs τ ∧ (∀ σ y, A.nrmInf σ τ f y ≤ 1) ∧ ∀ v e y, A.nrmFin v τ f e y ≤ 1}

def arVol : ℝ :=
  (limsup (fun τ : ℕ => ENNReal.log ((A.small τ).encard : ENNReal) *
    ((((Y.dim + 1).factorial : ℝ) / (τ : ℝ) ^ (Y.dim + 1) : ℝ) : EReal)) atTop).toReal / (Module.finrank ℚ F : ℝ)


open Classical in
def ht (x : Y.X) : ℝ :=
  -((∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x),
      (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z) / 2 -
        (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) +
    ∑ᶠ v : HeightOneSpectrum (𝓞 F), if h : Nonempty (Ext v) then
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v h.some y else 0) /
  (((A.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * (Nat.card {y : AlgPt Y // below y.1 = x} : ℝ))

def Induced (M : Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) : Prop :=
  (Function.support cf).Finite ∧
  ∃ r : (L.B.pull M.j).ι → Y.Fnˣ, Presents ((k : ℕ) • A.D) (L.B.pull M.j) r ∧
    (∀ (σ : F →+* ℂ) (y : Pts Y σ) (y' : CxPts M.p (σ.comp (algebraMap (𝓞 F) F))) (i : (L.B.pull M.j).ι) (f : Y.Fn),
      y'.1 = y.1 ≫ M.j → under y ∈ (L.B.pull M.j).U i → ((k : ℕ) • A.D).RegularAt (under y) f →
      Real.exp (-(2 * (k : ℕ) * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
          C.pn Y σ _ (C.mPow Y σ A.D k (A.m σ)) (C.cx Y σ f) y =
        ‖ratVal (f * (r i : Y.Fn)) y‖ ^ 2 * Real.exp (-(L.φ _).φ (i PUnit.unit) y')) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X) (i : (L.B.pull M.j).ι),
      spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit) →
      (k : ℕ) * A.lg v e y =
        Real.log (e.w (valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r i : Y.Fnˣ) : Y.Fn))) - (k : ℕ) * (A.n : ℕ) * cf v

def IsArTop (t : ℝ) : Prop :=
  ∃ (M : Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) (a : ℝ), A.Induced M L k cf ∧
    (haveI := M.ar.isIntegral; L.IsSelfInter a) ∧
    t = (a / (((k : ℕ) : ℝ) * (A.n : ℕ)) ^ (Y.dim + 1) + ((Y.dim : ℝ) + 1) * A.deg * ∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ)


open Classical in
def arTop : ℝ := if h : ∃ t, A.IsArTop t then h.choose else 0

def SemiPos : Prop := ∀ σ, C.mSmooth Y σ A.D (A.m σ) ∧ C.mPsh Y σ A.D (A.m σ) 0

def NefFib : Prop := ∃ (M : Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
  A.Induced M L k cf ∧ ArInt.NefFib L

def Nef : Prop := A.SemiPos ∧ A.NefFib ∧ ∀ x : Y.X, IsClosed ({x} : Set Y.X) → 0 ≤ A.ht x

variable {A}

end Adl

namespace Base

theorem ringKrullDim_integers : ringKrullDim (𝓞 F) = 1 := by
  refine eq_of_le_of_not_lt ?_ fun h' => RingOfIntegers.not_isField F ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    exact Ring.krullDimLE_one_iff_of_noZeroDivisors.2 fun I hI hP => hP.isMaximal hI
  · have h'' : ringKrullDim (𝓞 F) ≤ 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
    exact Ring.KrullDimLE.isField_of_isDomain

theorem isArithVar_pspace (n : ℕ) : IsArithVar (PSpace.str (𝓞 F) n) n := by
  have := ProjSpace.isIntegral_of_isDomain (𝓞 F) n
  have hc : ∀ i, topologicalKrullDim (ProjSpace.chart (𝓞 F) n i : Set (PSpace (𝓞 F) n)) = (n + 1 : ℕ) := fun i => by
    rw [topologicalKrullDim_eq_of_isEmbedding (ProjSpace.chartι (𝓞 F) n i).isOpenEmbedding.isEmbedding
      (congrArg SetLike.coe (ProjSpace.opensRange_chartι (𝓞 F) n i))]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
      (R := MvPolynomial {j // j ≠ i} (𝓞 F))).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_integers]
    simp [add_comm]
  have : Smooth (PSpace.str (𝓞 F) n) := SmoothOfRelativeDimension.smooth n _
  have : Flat (spMap (Int.castRingHom (𝓞 F))) := (ArithBase.isArithVar_id ringKrullDim_integers).flat
  refine ⟨inferInstance, inferInstance, ‹_›, ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩, inferInstance,
    le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
      ((hc 0).ge.trans (topologicalKrullDim_subspace_le _ _))⟩
  obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart (𝓞 F) n x
  exact ⟨_, (ProjSpace.chart (𝓞 F) n i).isOpen, hi, (hc i).le⟩

theorem valAt_stalk {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)
    (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dite_eq_left h]
  exact congrArg _ (IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec)

theorem isEqn_eqn {Z : Scheme.{0}} [IsIntegral Z] (Δ : CartierDiv Z) (x : Z) : Δ.IsEqn x (eqn Δ x) :=
  (Δ.exists_isEqn x).choose_spec



end Base

open Base


namespace Adl

variable {C : CxSt F} {Y : Var F} {A : Adl C Y} {M : Model Y} {L : HermLB M.p} {k : ℕ+}
  {cf : HeightOneSpectrum (𝓞 F) → ℝ}


variable (C Y) in
def triv : Adl C Y where
  D := 0
  n := 1
  m σ := C.ofWeight Y σ 0 (LB.triv Y.X) (fun _ => 1) presents_zero (Weight.ofFun fun _ => 0)
  ci := 0
  lg _ e y := -Real.log (e.w (valAt y.1 (eqn (0 : Y.Dv) (below y.1) : Y.Fn)))


end Adl

variable [StarRing F]


open Classical in
def frameAt (W : HLat F) (σ : F →+* ℂ) : Matrix W.ι W.ι ℂ :=
  if (InfinitePlace.mk σ).embedding = σ then W.X (InfinitePlace.mk σ) else (W.X (InfinitePlace.mk σ)).map (starRingEnd ℂ)

def ofW (C : CxSt F) (Y : Var F) (L : Y.Dv) (W : HLat F) (ι : W.V →ₗ[F] Y.Fn) : Adl C Y where
  D := L
  n := 1
  m σ := C.fsMet Y σ L fun k : W.ι => ∑ i, frameAt W σ i k • C.cx Y σ (ι (W.b i))
  ci := 0
  lg _ e y := -Real.log (⨆ x : W.L, e.w (valAt y.1 (ι x * (eqn L (below y.1) : Y.Fn))))

structure CutSt (C : CxSt F) : Type 1 where

  cutGood : ∀ Y : Var F, Y.Cl → ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Y.Fn) → (Fin Y.dim → Fin n → 𝓞 E) → Prop

  cutHt : ∀ Y : Var F, Adl C Y → ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Y.Fn) → (Fin Y.dim → Fin n → 𝓞 E) → ℝ

  cutOrd : ∀ (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Y.Fn) → (Fin Y.dim → Fin n → 𝓞 E) → Y.Dv → Y.Fn → ℕ

structure ResSt (C : CxSt F) : Type 1 where

  resFull : ∀ (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Y.Fn) → (Fin Y.dim → Fin n → 𝓞 E) → ∀ (M0 : HLat F), (M0.V →ₗ[F] Y.Fn) → Adl C Y → Prop

  resDeg : ∀ (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Y.Fn) → (Fin Y.dim → Fin n → 𝓞 E) → ∀ (M0 : HLat F), (M0.V →ₗ[F] Y.Fn) → Adl C Y → ℝ


omit [StarRing F] in
theorem supInf_twist {C : CxSt F} {Y : Var F} (A : Adl C Y) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) (v : InfinitePlace F) (τ : ℕ) (f : Y.Fn) :
    (A.twist ci cf).supInf v τ f = Real.exp (-((τ : ℝ) * ci v)) * A.supInf v τ f := by
  unfold Adl.supInf
  rw [Real.mul_iSup_of_nonneg (Real.exp_pos _).le]
  refine congrArg _ (funext fun y => ?_)
  simp only [Adl.nrmInf, Adl.twist, InfinitePlace.mk_embedding, Pi.add_apply]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring


omit [StarRing F] in
theorem supFin_twist {C : CxSt F} {Y : Var F} (A : Adl C Y) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) (v : HeightOneSpectrum (𝓞 F)) (τ : ℕ) (f : Y.Fn) :
    (A.twist ci cf).supFin v τ f = Real.exp (-((τ : ℝ) * cf v)) * A.supFin v τ f := by
  unfold Adl.supFin
  rw [Real.mul_iSup_of_nonneg (Real.exp_pos _).le]
  refine congrArg _ (funext fun q => ?_)
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  simp only [Adl.nrmFin, Adl.twist]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  field_simp
  ring

theorem supInf_ofW (C : CxSt F) (Y : Var F) (L : Y.Dv) (W : HLat F) (ι : W.V →ₗ[F] Y.Fn) (v : InfinitePlace F) (τ : ℕ)
    (f : Y.Fn) : (ofW C Y L W ι).supInf v τ f =
      ⨆ y, Real.sqrt (C.pn Y v.embedding (τ • L) (C.mPow Y v.embedding L τ
        (C.fsMet Y v.embedding L (fun k : W.ι => ∑ i, (W.X v) i k • C.cx Y v.embedding (ι (W.b i)))))
        (C.cx Y v.embedding f) y) := by
  unfold Adl.supInf
  refine congrArg _ (funext fun y => ?_)
  have e : frameAt W v.embedding = W.X v := by simp [frameAt]
  simp [Adl.nrmInf, ofW, e, Real.sqrt_eq_rpow]

def geoOf (C : CxSt F) (_K : CutSt C) (_R : ResSt C) : DV.Geo F where
  Var := Var F
  dim := Var.dim
  Fn := Var.Fn
  Dv := Var.Dv
  H0 := Var.H0
  Cl := Var.Cl
  supp := Var.supp
  inter := Var.inter
  vanishOn := Var.vanishOn
  Adl := Adl C
  ofW := ofW C
  twist := fun _ => Adl.twist
  arTop := fun _ => Adl.arTop
  arVol := fun _ => Adl.arVol
  nefA := fun _ => Adl.Nef

theorem deg_ofW (C : CxSt F) (Y : Var F) (L : Y.Dv) (W : HLat F) (ι : W.V →ₗ[F] Y.Fn) :
    (ofW C Y L W ι).deg = (Y.inter (fun _ => L) : ℝ) := by simp [Adl.deg, ofW]


omit [StarRing F] in
theorem deg_twist {C : CxSt F} {Y : Var F} (A : Adl C Y) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) : (A.twist ci cf).deg = A.deg := rfl




end GlobalTheory.TrueGeo
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers =====
