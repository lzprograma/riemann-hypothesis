module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
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
import Mathlib.RingTheory.Valuation.Integral
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

@[expose] public section

noncomputable section

open ValuativeRel Polynomial UpperTheory.V.Hi

namespace UpperTheory.V.Z.Sym.Sig

open Loc Glob

section Alg

variable {K : Type} [Field K] {τ a b : K}

private theorem ev_star (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hs : a + b = τ)
    (x : Etau K τ) : ev ha (star x) = ev hb x := by
  show (star x).re + a * (star x).im = x.re + b * x.im
  rw [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  linear_combination (-x.im) * hs

private theorem ev_quo (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hs : a + b = τ)
    (z : (Etau K τ)ˣ) : ev ha (quo z) = ((evU ha z / evU hb z : Kˣ) : K) := by
  show ev ha ((z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) = _
  rw [map_mul, ev_star ha hb hs, div_eq_mul_inv, ← map_inv, Units.val_mul]
  rfl

private def evE (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b) :
    Etau K τ ≃ₐ[K] K × K :=
  have h : ((a, b) : K × K) * (a, b) = (-1 : K) • 1 + τ • (a, b) := by
    ext <;> simp [ha, hb] <;> ring
  { QuadraticAlgebra.lift ⟨(a, b), h⟩ with
    invFun := fun p => ⟨p.1 - a * ((p.1 - p.2) / (a - b)), (p.1 - p.2) / (a - b)⟩
    left_inv := fun z => by
      have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
      ext
      · dsimp [QuadraticAlgebra.lift]; field_simp; ring
      · dsimp [QuadraticAlgebra.lift]; field_simp; ring
    right_inv := fun p => by
      have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
      ext
      · dsimp [QuadraticAlgebra.lift]; ring
      · dsimp [QuadraticAlgebra.lift]; field_simp; ring }

private theorem evE_apply (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1)
    (hab : a ≠ b) (x : Etau K τ) : evE ha hb hab x = (ev ha x, ev hb x) := by
  ext <;> simp [evE, QuadraticAlgebra.lift, ev, mul_comm]

end Alg

theorem roots : Roots := by
  intro k _ _ _ _ O _ _ hO a ha1
  have hl := root_left (K := k) a
  have hr := root_right (K := k) a
  have hs : (a : k) + ((a⁻¹ : kˣ) : k) = (a : k) + ((a⁻¹ : kˣ) : k) := rfl
  have hs' : ((a⁻¹ : kˣ) : k) + (a : k) = (a : k) + ((a⁻¹ : kˣ) : k) := add_comm _ _
  have hab : (a : k) ≠ ((a⁻¹ : kˣ) : k) := by
    intro h
    have h2 : valuation k (a : k) * valuation k (a : k) = 1 := by
      rw [← map_mul]
      nth_rewrite 2 [h]
      rw [Units.mul_inv, map_one]
    have h3 := pow_lt_one₀ zero_le' ha1 (n := 2) two_ne_zero
    rw [sq, h2] at h3
    exact lt_irrefl _ h3
  have hint : (valuation k).Integers O :=
    ⟨hO.inj, fun x => (hO.range _).mp ⟨x, rfl⟩, fun r hr => (hO.range r).mpr hr⟩
  let e : (Etau k ((a : k) + (a⁻¹ : kˣ)))ˣ ≃* kˣ × kˣ :=
    (Units.mapEquiv (evE hl hr hab).toMulEquiv).trans MulEquiv.prodUnits
  let eO : Etau k ((a : k) + (a⁻¹ : kˣ)) ≃ₐ[O] k × k :=
    { (evE hl hr hab).toRingEquiv with
      commutes' := fun r => by
        change evE hl hr hab (algebraMap O _ r) = algebraMap O (k × k) r
        rw [evE_apply, Prod.algebraMap_apply]
        refine Prod.ext (by show algebraMap O k r + _ * 0 = algebraMap O k r; ring)
          (by show algebraMap O k r + _ * 0 = algebraMap O k r; ring) }
  refine ⟨fun t => ⟨e.symm (t, 1), Units.ext (by
    have he := e.apply_symm_apply (t, 1)
    have h1 : ((evU hl (e.symm (t, 1)) : kˣ) : k) = ((e (e.symm (t, 1))).1 : k) := by
      show ev hl _ = (evE hl hr hab _).1
      rw [evE_apply]
    have h2 : ((evU hr (e.symm (t, 1)) : kˣ) : k) = ((e (e.symm (t, 1))).2 : k) := by
      show ev hr _ = (evE hl hr hab _).2
      rw [evE_apply]
    rw [MonoidHom.div_apply, Units.val_div_eq_div_val, h1, h2, he]
    simp)⟩,
    ?_, fun z => ⟨ev_quo hl hr hs z, ev_quo hr hl hs' z⟩⟩
  ext z
  show (IsIntegral O (quo z) ∧ IsIntegral O (quo z⁻¹)) ↔
    valuation k (((evU hl / evU hr) z : kˣ) : k) = 1
  rw [MonoidHom.div_apply]
  have q1 : ev hl (quo z) = ((evU hl z / evU hr z : kˣ) : k) := ev_quo hl hr hs z
  have q2 : ev hr (quo z) = ((evU hr z / evU hl z : kˣ) : k) := ev_quo hr hl hs' z
  have q3 : ev hl (quo z⁻¹) = ((evU hr z / evU hl z : kˣ) : k) := by
    rw [ev_quo hl hr hs z⁻¹, map_inv, map_inv, inv_div_inv]
  have q4 : ev hr (quo z⁻¹) = ((evU hl z / evU hr z : kˣ) : k) := by
    rw [ev_quo hr hl hs' z⁻¹, map_inv, map_inv, inv_div_inv]
  have hprod : valuation k ((evU hl z / evU hr z : kˣ) : k) *
      valuation k ((evU hr z / evU hl z : kˣ) : k) = 1 := by
    rw [← map_mul, ← Units.val_mul, div_mul_div_comm, mul_comm (evU hr z) (evU hl z),
      div_self', Units.val_one, map_one]
  have int_iff : ∀ w : Etau k ((a : k) + (a⁻¹ : kˣ)),
      IsIntegral O w ↔ valuation k (ev hl w) ≤ 1 ∧ valuation k (ev hr w) ≤ 1 := fun w => by
    rw [← isIntegral_algEquiv eO, IsIntegral.pair_iff,
      hint.isIntegral_iff_v_le_one, hint.isIntegral_iff_v_le_one]
    change valuation k (evE hl hr hab w).1 ≤ 1 ∧ valuation k (evE hl hr hab w).2 ≤ 1 ↔ _
    rw [evE_apply]
  rw [int_iff, int_iff, q1, q2, q3, q4]
  constructor
  · rintro ⟨⟨v1, v2⟩, -⟩
    refine le_antisymm v1 ?_
    calc (1 : ValueGroupWithZero k) = _ := hprod.symm
      _ ≤ valuation k ((evU hl z / evU hr z : kˣ) : k) * 1 := by gcongr
      _ = _ := mul_one _
  · intro hv
    rw [hv, one_mul] at hprod
    exact ⟨⟨hv.le, hprod.le⟩, ⟨hprod.le, hv.le⟩⟩

end UpperTheory.V.Z.Sym.Sig

end
