module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.ContraPair
open GlobalTheory.ThetaPull (cFin pInf_conjAd pFin_conjAd conjAd_conjAd continuous_conjAd)
open scoped ContDiff

namespace GlobalTheory.BarPull

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

theorem map_map_comm (p : R →+* S) (c : R →+* R) (c' : S →+* S) (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map p g) :=
  GlobalTheory.IsoPull.map_map_comm p p c c' h g

theorem continuous_mapGL [TopologicalSpace R] [IsTopologicalRing R] (c : R →+* R) (h : Continuous c) :
    Continuous (GeneralLinearGroup.map (n := Fin a) c) :=
  GlobalTheory.IsoPull.continuous_mapGL c h

theorem map_unip {r : ℕ} (c : R →+* R) (x : BlockIx a r → R) :
    GeneralLinearGroup.map c (unip x) = unip fun p => c (x p) :=
  GlobalTheory.IsoPull.map_unip c x

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

omit [IsCMField E] in
def barL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => star (X i j)
      map_add' := fun X Y => by funext i j; simp
      map_smul' := fun t X => by funext i j; simp }

omit [IsCMField E] in
theorem height_bar (y : GL (Fin a) (Cinf E)) :
    height (GeneralLinearGroup.map (starRingEnd (Cinf E)) y) = height y := by
  have h1 : ∀ y : GL (Fin a) (Cinf E), ‖toL (GeneralLinearGroup.map (starRingEnd (Cinf E)) y).val‖ = ‖toL y.val‖ :=
    fun y => norm_star (toL y.val)
  unfold height
  rw [← map_inv, h1, h1]

theorem bar_mem_ratN {r : ℕ} {x : BlockIx a r → Ad E} (hx : x ∈ ratN E a r) :
    (fun p => conjAd E (x p)) ∈ ratN E a r := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => IsCMField.complexConj E (y p), funext fun p => (conjAd_algebraMap (y p)).symm⟩

def barData (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) :
    GlobalTheory.IsoPull.PullData E E a where
  eRat := (IsCMField.complexConj E).toRingEquiv.toRingHom
  eAd :=
    { toFun := conjAd E
      invFun := conjAd E
      left_inv := conjAd_conjAd
      right_inv := conjAd_conjAd
      map_mul' := map_mul (conjAd E)
      map_add' := map_add (conjAd E) }
  cont_eAd := continuous_conjAd
  cont_eAd_symm := continuous_conjAd
  eAd_alg x := conjAd_algebraMap x
  eAd_rat := bar_mem_ratN
  eAd_symm_rat := bar_mem_ratN
  eInf := starRingEnd (Cinf E)
  eFin := cFin E
  cont_eFin := continuous_conjFin _
  pInf_eAd := pInf_conjAd
  pFin_eAd := pFin_conjAd
  mapL := barL
  mapL_apply _ _ _ := rfl
  mapOp := conjOp
  mapOp_fin _ := rfl
  mapOp_cpt k := ⟨barK k, rfl, Units.ext rfl⟩
  mapOp_lie _ := rfl
  height_le := ⟨1, le_rfl, fun y => by rw [one_mul, height_bar]⟩
  embMap := ComplexEmbedding.conjugate
  eInf_atEmb τ z := by
    classical
    change star (atEmb τ z) = atEmb (ComplexEmbedding.conjugate τ) z
    rw [atEmb_conj]
    unfold atEmb
    rw [Pi.star_single]
    split_ifs <;> rfl

variable (E a) in
def barA : GA E a →* GA E a := GeneralLinearGroup.map (conjAd E)

theorem barA_barA (g : GA E a) : barA E a (barA E a g) = g := by
  ext i j : 2
  exact conjAd_conjAd _

theorem barA_infGL (y : GL (Fin a) (Cinf E)) :
    barA E a (infGL E a y) = infGL E a (GeneralLinearGroup.map (starRingEnd (Cinf E)) y) :=
  (barData E a).mapA_infGL y

theorem barA_finGL (k : GL (Fin a) (Af E)) : barA E a (finGL E a k) = finGL E a (GeneralLinearGroup.map (cFin E) k) :=
  (barData E a).mapA_finGL k

theorem barA_ratGL (γ : GL (Fin a) E) :
    barA E a (ratGL E a γ) =
      ratGL E a (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom γ) :=
  (barData E a).mapA_ratGL γ

theorem chart_bar (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => φ (barA E a g)) g x = chart φ (barA E a g) (barL x) ∧ barL x ∈ invSet E a :=
  (barData E a).chart_map φ g hx

theorem bar_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : (fun g => φ (barA E a g)) ∈ Sm E a :=
  (barData E a).map_mem_Sm hφ

variable (E a) in
def pull : Sm E a ≃ₗ[ℂ] Sm E a := (barData E a).pull bar_mem_Sm

theorem pull_apply (φ : Sm E a) (g : GA E a) : (pull E a φ).1 g = φ.1 (barA E a g) := rfl

theorem pull_pull (φ : Sm E a) : pull E a (pull E a φ) = φ := (pull E a).left_inv φ

theorem rt_pull (h : GA E a) (φ : Sm E a) : rt E a h (pull E a φ) = pull E a (rt E a (barA E a h) φ) :=
  (barData E a).rt_pull h φ

theorem lie_pull (X : Lie E a) (φ : Sm E a) : lie E a X (pull E a φ) = pull E a (lie E a (barL X) φ) :=
  (barData E a).lie_pull X φ

theorem act_pull (o : Op E a) (φ : Sm E a) : act o (pull E a φ) = pull E a (act (conjOp o) φ) :=
  (barData E a).act_pull o φ

theorem pull_act (o : Op E a) (φ : Sm E a) : pull E a (act o φ) = act (conjOp o) (pull E a φ) := by
  conv_lhs => rw [← pull_pull φ, act_pull, pull_pull]

theorem Eop_pull (τ : E →+* ℂ) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (pull E a φ) = pull E a (Eop (ComplexEmbedding.conjugate τ) i j φ) :=
  (barData E a).Eop_pull τ i j φ

theorem cap_pull (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (pull E a φ) = pull E a (cap (ComplexEmbedding.conjugate τ) u φ) :=
  (barData E a).cap_pull τ u φ

theorem Zalg_pull {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (pull E a φ) = pull E a (z' φ) :=
  (barData E a).Zalg_pull hz

theorem isAutForm_pull {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (pull E a φ) :=
  (barData E a).isAutForm_pull h

theorem isCuspidal_pull {φ : GA E a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (barA E a g) :=
  (barData E a).isCuspidal_pull hφ

end GlobalTheory.BarPull

end
