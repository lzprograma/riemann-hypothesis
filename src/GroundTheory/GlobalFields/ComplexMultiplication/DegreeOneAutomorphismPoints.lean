module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Isogeny
public import GroundTheory.GlobalFields.ComplexMultiplication.WeberFunction
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyRamification
public import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDescent
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
public import GroundTheory.GlobalFields.ComplexMultiplication.DualDescentBase
public import GroundTheory.GlobalFields.ComplexMultiplication.IsogenyDegreeOne
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsOrd
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyPoints
public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionIso
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialBaseChange
public import GroundTheory.GlobalFields.ComplexMultiplication.WeberFunctionAutomorphisms
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.SupersingularPowField
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsValuation
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphism, GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismPoints

-- ===== clump member: GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphism =====
-- clump-header: {"m": "GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphism", "h": "module\n\npublic import GroundTheory.ArithmeticGeometry.AbelianVarieties.Isogeny\npublic import GroundTheory.GlobalFields.ComplexMultiplication.WeberFunction\nimport GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsValuation\npublic import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyRamification\npublic import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDescent\npublic import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField\npublic import GroundTheory.GlobalFields.ComplexMultiplication.DualDescentBase\npublic import GroundTheory.GlobalFields.ComplexMultiplication.IsogenyDegreeOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsOrd\npublic import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate\npublic import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyPoints\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
  GroundTheory.Arith.Abelian

universe u

section AlgClosed

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

theorem exists_scale_of_degree_eq_one_of_isAlgClosed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hA : IsShortForm A) (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ α γ : F, α ≠ 0 ∧ γ ≠ 0 ∧
      ψ.x = algebraMap F A.toAffine.FunctionField α * genX A ∧
      ψ.y = algebraMap F A.toAffine.FunctionField γ * genY A ∧
      γ ^ 2 = α ^ 3 ∧ γ ^ 2 * A.a₄ = B.a₄ * α ∧ γ ^ 2 * A.a₆ = B.a₆ := by
  obtain ⟨α, β, γ, δ, ε, hα, hγ, hx, hy, c3, c2, c1, c0, d1, d0⟩ :=
    exists_coeffs_of_degree_eq_one_of_isAlgClosed ψ h
  rw [hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, hB.a₁_eq, hB.a₂_eq, hB.a₃_eq] at *
  have hδ : δ = 0 := by
    have : (2 * γ) * δ = 0 := by linear_combination d1
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hγ)
  have hε : ε = 0 := by
    have : (2 * γ) * ε = 0 := by linear_combination d0
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hγ)
  subst hδ hε
  have hβ : β = 0 := by
    have : (3 * α ^ 2) * β = 0 := by linear_combination -c2
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h3 (pow_ne_zero 2 hα))
  subst hβ
  refine ⟨α, γ, hα, hγ, by simpa using hx, by simpa using hy, c3, by linear_combination c1,
    by linear_combination c0⟩

end AlgClosed

section General

variable {F : Type u} [Field F] {A B : WeierstrassCurve F} [A.IsElliptic] [B.IsElliptic]

omit [A.IsElliptic] in
theorem IsShortForm.baseChange {W : WeierstrassCurve F} (hW : IsShortForm W) (L : Type*) [Field L]
    [Algebra F L] : IsShortForm (W.baseChange L) :=
  ⟨by simp [WeierstrassCurve.baseChange, hW.a₁_eq], by simp [WeierstrassCurve.baseChange, hW.a₂_eq],
    by simp [WeierstrassCurve.baseChange, hW.a₃_eq]⟩

theorem exists_scale_of_degree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hA : IsShortForm A)
    (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ u : Fˣ, ψ.x = algebraMap F A.toAffine.FunctionField ((u : F) ^ 2) * genX A ∧
      ψ.y = algebraMap F A.toAffine.FunctionField ((u : F) ^ 3) * genY A ∧
      B.a₄ = (u : F) ^ 4 * A.a₄ ∧ B.a₆ = (u : F) ^ 6 * A.a₆ := by
  classical
  let Ω := AlgebraicClosure F
  have hd : (isogBaseChange (F' := Ω) ψ).degree = 1 := by rw [degree_isogBaseChange, h]
  have inj := (algebraMap F Ω).injective
  have h2' : (2 : Ω) ≠ 0 := by
    have := (_root_.map_ne_zero (algebraMap F Ω)).mpr h2
    rwa [map_ofNat] at this
  have h3' : (3 : Ω) ≠ 0 := by
    have := (_root_.map_ne_zero (algebraMap F Ω)).mpr h3
    rwa [map_ofNat] at this
  obtain ⟨α, γ, hα, hγ, hx, hy, hc, h4, h6⟩ := exists_scale_of_degree_eq_one_of_isAlgClosed h2' h3'
    (hA.baseChange Ω) (hB.baseChange Ω) _ hd
  rw [isogBaseChange_alt, ← bcEmb_genX] at hx
  rw [isogBaseChange_y, ← bcEmb_genY] at hy
  have hX0 : genX A ≠ 0 := fun h => transcendental_genX A (h ▸ isAlgebraic_zero)
  have hY0 : genY A ≠ 0 := genY_ne_zero A
  set K' := (A.baseChange Ω).toAffine.FunctionField
  have hXb : bcEmb (F' := Ω) A (genX A) ≠ 0 := (_root_.map_ne_zero _).mpr hX0
  have hYb : bcEmb (F' := Ω) A (genY A) ≠ 0 := (_root_.map_ne_zero _).mpr hY0
  have ex : bcEmb (F' := Ω) A (ψ.x / genX A) = algebraMap Ω K' α := by
    rw [map_div₀, hx, mul_div_cancel_right₀ _ hXb]
  have ey : bcEmb (F' := Ω) A (ψ.y / genY A) = algebraMap Ω K' γ := by
    rw [map_div₀, hy, mul_div_cancel_right₀ _ hYb]
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_bcEmb A ex
  obtain ⟨c, hc'⟩ := exists_algebraMap_eq_of_bcEmb A ey
  have key : ∀ (b : F) (f : A.toAffine.FunctionField) (β : Ω),
      algebraMap F A.toAffine.FunctionField b = f → bcEmb (F' := Ω) A f = algebraMap Ω K' β →
        algebraMap F Ω b = β := by
    intro b f β hb hf
    apply (algebraMap Ω K').injective
    rw [← hf, ← hb, AlgHom.commutes, IsScalarTower.algebraMap_apply F Ω K']
  have haα := key a _ α ha ex
  have hcγ := key c _ γ hc' ey
  have ha0 : a ≠ 0 := by rintro rfl; exact hα (by rw [← haα, map_zero])
  have hc0 : c ≠ 0 := by rintro rfl; exact hγ (by rw [← hcγ, map_zero])
  have hca : c ^ 2 = a ^ 3 := inj (by rw [map_pow, map_pow, haα, hcγ, hc])
  have h4' : c ^ 2 * A.a₄ = B.a₄ * a := inj (by
    rw [map_mul, map_mul, map_pow, haα, hcγ]; exact h4)
  have h6' : c ^ 2 * A.a₆ = B.a₆ := inj (by
    rw [map_mul, map_pow, hcγ]; exact h6)
  let v : Fˣ := Units.mk0 (c / a) (div_ne_zero hc0 ha0)
  have hv2 : (v : F) ^ 2 = a := by
    show (c / a) ^ 2 = a
    field_simp
    linear_combination hca
  have hv3 : (v : F) ^ 3 = c := by
    show (c / a) ^ 3 = c
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
    rw [div_pow, ← hca, div_eq_iff hc2]
    ring
  have hv0 : (v : F) ^ 2 ≠ 0 := pow_ne_zero 2 v.ne_zero
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · rw [hv2, ha, div_mul_cancel₀ _ hX0]
  · rw [hv3, hc', div_mul_cancel₀ _ hY0]
  · apply mul_right_cancel₀ hv0
    rw [hv2, ← h4', ← hv3, ← hv2]
    ring
  · rw [← h6', ← hv3]
    ring

end General

end GroundTheory.Global
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphism =====

-- ===== clump member: GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismPoints =====
-- clump-header: {"m": "GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismPoints", "h": "module\n\npublic import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionIso\npublic import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialBaseChange\npublic import GroundTheory.GlobalFields.ComplexMultiplication.WeberFunctionAutomorphisms\npublic import GroundTheory.ArithmeticGeometry.AbelianVarieties.SupersingularPowField\npublic import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDescent\npublic import GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphism\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

theorem pow_eq_one_of_scale {F : Type*} [Field F] {E : WeierstrassCurve F} [E.IsElliptic]
    (hE : IsShortForm E) {u : F} (h4 : E.a₄ = u ^ 4 * E.a₄) (h6 : E.a₆ = u ^ 6 * E.a₆) :
    u ^ automorphismOrder E = 1 ∧ u ^ 12 = 1 := by
  by_cases hu : u = 0
  · subst hu
    rcases hE.a₄_ne_zero_or_a₆_ne_zero with h | h
    · exact absurd (by simpa using h4) h
    · exact absurd (by simpa using h6) h
  have hn : u ^ automorphismOrder E = 1 := by
    have := (scale_conditions_iff hE u⁻¹).mp ⟨by rw [inv_inv]; exact h4.symm,
      by rw [inv_inv]; exact h6.symm⟩
    rwa [inv_pow, inv_eq_one] at this
  refine ⟨hn, ?_⟩
  unfold automorphismOrder at hn
  split_ifs at hn
  · rw [show 12 = 4 * 3 by rfl, pow_mul, hn, one_pow]
  · rw [show 12 = 6 * 2 by rfl, pow_mul, hn, one_pow]
  · rw [show 12 = 2 * 6 by rfl, pow_mul, hn, one_pow]

section AlgClosed

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]


omit [IsAlgClosed F] [A.IsElliptic] [B.IsElliptic] in
theorem vcPoint_constPoint (C : VariableChange F) (hC : C • A = B) (R : A.toAffine.Point) :
    vcPoint (C.baseChange A.toAffine.FunctionField) (Elliptic.baseChange_smul_eq C _ hC)
        (constPoint A R) = constMap B A.toAffine.FunctionField (vcPoint C hC R) := by
  cases R with
  | zero => rfl
  | some x y h =>
    obtain ⟨h', e⟩ := constPoint_some A h
    rw [e, vcPoint_some, vcPoint_some]
    show Point.some _ _ _ = Point.some _ _ _
    rw [Point.some.injEq]
    exact ⟨(map_vcX C (algebraMap F _) x).symm, (map_vcY C (algebraMap F _) x y).symm⟩

theorem pointMap_eq_vcPoint (C : VariableChange F) (hC : C • A = B) (ψ : Isogeny A B)
    (hψ : ψ.1 = vcPoint (C.baseChange A.toAffine.FunctionField)
      (Elliptic.baseChange_smul_eq C _ hC) (genericPoint A)) (R : A.toAffine.Point) :
    ψ.pointMap R = vcPoint C hC R := by
  apply Isogeny.pointMap_eq_of_map_translate
  rw [hψ, Elliptic.map_vcPoint C (translate A R) hC, map_translate_genericPoint, vcPoint_add,
    vcPoint_constPoint]

theorem pointMap_some_of_scale (hA : IsShortForm A) (hB : IsShortForm B) (u : Fˣ)
    (h4 : B.a₄ = (u : F) ^ 4 * A.a₄) (h6 : B.a₆ = (u : F) ^ 6 * A.a₆) (ψ : Isogeny A B)
    (hx : ψ.x = algebraMap F A.toAffine.FunctionField ((u : F) ^ 2) * genX A)
    (hy : ψ.y = algebraMap F A.toAffine.FunctionField ((u : F) ^ 3) * genY A)
    {x y : F} (h : A.toAffine.Nonsingular x y) :
    ∃ h' : B.toAffine.Nonsingular ((u : F) ^ 2 * x) ((u : F) ^ 3 * y),
      ψ.pointMap (.some x y h) = .some _ _ h' := by
  let C : VariableChange F := ⟨u⁻¹, 0, 0, 0⟩
  have hC : C • A = B := by
    ext
    · simp [C, variableChange_a₁, hA.a₁_eq, hB.a₁_eq]
    · simp [C, variableChange_a₂, hA.a₁_eq, hA.a₂_eq, hB.a₂_eq]
    · simp [C, variableChange_a₃, hA.a₁_eq, hA.a₃_eq, hB.a₃_eq]
    · simp [C, variableChange_a₄, hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, h4]
    · simp [C, variableChange_a₆, hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, h6]
  have hψ : ψ.1 = vcPoint (C.baseChange A.toAffine.FunctionField)
      (Elliptic.baseChange_smul_eq C _ hC) (genericPoint A) := by
    rw [ψ.val_eq_some_x_y]
    simp only [GroundTheory.Arith.Abelian.genericPoint, vcPoint_some, Point.some.injEq]
    constructor
    · rw [hx]
      simp [C, vcX, VariableChange.baseChange, VariableChange.map]
    · rw [hy]
      simp [C, vcY, VariableChange.baseChange, VariableChange.map]
  have ex : vcX C x = (u : F) ^ 2 * x := by simp [C, vcX]
  have ey : vcY C x y = (u : F) ^ 3 * y := by simp [C, vcY]
  have hN : B.toAffine.Nonsingular (vcX C x) (vcY C x y) := hC ▸ (nonsingular_vc C A x y).2 h
  rw [ex, ey] at hN
  refine ⟨hN, ?_⟩
  rw [pointMap_eq_vcPoint C hC ψ hψ, vcPoint_some, Point.some.injEq]
  exact ⟨ex, ey⟩

end AlgClosed

section BaseChange

variable {F : Type u} [Field F] {A B : WeierstrassCurve F} [A.IsElliptic] [B.IsElliptic]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] [DecidableEq Ω]

theorem pointMap_isogBaseChange_some_of_degree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hA : IsShortForm A) (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ u : Fˣ, B.a₄ = (u : F) ^ 4 * A.a₄ ∧ B.a₆ = (u : F) ^ 6 * A.a₆ ∧
      ∀ (x y : Ω) (hxy : (A.baseChange Ω).toAffine.Nonsingular x y),
        ∃ h' : (B.baseChange Ω).toAffine.Nonsingular
            (algebraMap F Ω (u : F) ^ 2 * x) (algebraMap F Ω (u : F) ^ 3 * y),
          (isogBaseChange (F' := Ω) ψ).pointMap (.some x y hxy) = .some _ _ h' := by
  obtain ⟨u, hx, hy, h4, h6⟩ := exists_scale_of_degree_eq_one h2 h3 hA hB ψ h
  refine ⟨u, h4, h6, fun x y hxy => ?_⟩
  let v : Ωˣ := Units.map (algebraMap F Ω) u
  have hv : (v : Ω) = algebraMap F Ω (u : F) := rfl
  have h4' : (B.baseChange Ω).a₄ = (v : Ω) ^ 4 * (A.baseChange Ω).a₄ := by
    show algebraMap F Ω B.a₄ = _ * algebraMap F Ω A.a₄
    rw [h4, hv, map_mul, map_pow]
  have h6' : (B.baseChange Ω).a₆ = (v : Ω) ^ 6 * (A.baseChange Ω).a₆ := by
    show algebraMap F Ω B.a₆ = _ * algebraMap F Ω A.a₆
    rw [h6, hv, map_mul, map_pow]
  have hx' : (isogBaseChange (F' := Ω) ψ).x =
      algebraMap Ω (A.baseChange Ω).toAffine.FunctionField ((v : Ω) ^ 2) *
        genX (A.baseChange Ω) := by
    rw [isogBaseChange_alt, hx, map_mul, AlgHom.commutes, bcEmb_genX, hv, ← map_pow,
      ← IsScalarTower.algebraMap_apply]
  have hy' : (isogBaseChange (F' := Ω) ψ).y =
      algebraMap Ω (A.baseChange Ω).toAffine.FunctionField ((v : Ω) ^ 3) *
        genY (A.baseChange Ω) := by
    rw [isogBaseChange_y, hy, map_mul, AlgHom.commutes, bcEmb_genY, hv, ← map_pow,
      ← IsScalarTower.algebraMap_apply]
  exact pointMap_some_of_scale (hA.baseChange Ω) (hB.baseChange Ω) v h4' h6' _ hx' hy' hxy

end BaseChange

end GroundTheory.Global
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismPoints =====
