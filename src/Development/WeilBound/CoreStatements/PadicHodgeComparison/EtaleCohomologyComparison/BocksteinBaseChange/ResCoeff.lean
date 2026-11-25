module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ExistsDpPow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationSquareOfValuationMod

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobeniusElement, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobeniusElement =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobeniusElement", "h": "module\n\npublic import Mathlib.Algebra.Ring.Hom.Defs\npublic import Mathlib.Data.Nat.Prime.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Algebra.CharP.Lemmas\n\n"}
section -- clump:auto
@[expose] public section

noncomputable def UpperTheory.Reformulated.B.FrobeniusElement.frb :
    {l : ℕ} → [Fact (Nat.Prime l)] → {B₀ : Type} → [inst : CommRing B₀] → (↑l : B₀) = (0 : B₀) → B₀ →+* B₀ :=
  fun {l} [hl : Fact (Nat.Prime l)] {B₀} [CommRing B₀] h =>
    { toFun := fun x => x ^ l
      map_one' := one_pow l
      map_mul' := fun x y => mul_pow x y l
      map_zero' := zero_pow hl.out.ne_zero
      map_add' := fun x y => by
        obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl.out x y
        rw [hr, h]
        ring }
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobeniusElement =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobeniusElement\npublic import Mathlib.RingTheory.WittVector.Isocrystal\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationSquareOfValuationMod\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ExistsDpPow\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison

namespace Wc

def basePt {O : Type} [CommRing O] (F : B.Fn O) {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁} {κ₂ : O →+* k₂}
    (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) : F.ptK κ₂ ⟶ F.ptK κ₁ where
  app B₀ := TypeCat.ofHom fun z => ⟨(z.1.1.comp τ, z.1.2), by rw [RingHom.comp_assoc, h]; exact z.2⟩
  naturality _ _ _ := rfl

noncomputable def frb {l : ℕ} [Fact l.Prime] {B₀ : Type} [CommRing B₀] (h : (l : B₀) = 0) : B₀ →+* B₀ :=
  _root_.UpperTheory.Reformulated.B.FrobeniusElement.frb h

theorem idc {Λ S : Type} [CommRing Λ] [CommRing S] (c : Λ →+* S) (a : Λ) : RingHom.id S (c a) = c (RingHom.id Λ a) := rfl

variable (l : ℕ) [hl : Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l]

abbrev Wm (m : ℕ) : Type := WittVector l k ⧸ Ideal.span {(l : WittVector l k) ^ m}

abbrev Im (m : ℕ) : Ideal (Wm l k m) := (Ideal.span {(l : WittVector l k)}).map (Ideal.Quotient.mk _)

def pd (m : ℕ) : DividedPowers (Im l k m) := (exists_pd_l l (witt_unit l k) (witt_tf l k) m).choose

theorem isPd (m : ℕ) : R.IsPd (Ideal.Quotient.mk _) (Ideal.span {(l : WittVector l k)}) (pd l k m) :=
  (exists_pd_l l (witt_unit l k) (witt_tf l k) m).choose_spec

abbrev bs (m : ℕ) : Base where
  R := Wm l k m
  I := Im l k m
  γ := pd l k m
  t := 1
  p := l

def res (m : ℕ) : k →+* Wm l k m ⧸ Im l k m :=
  (WittVector.constantCoeff (p := l) (R := k)).liftOfSurjective (WittVector.constantCoeff_surjective l)
    ⟨(Ideal.Quotient.mk _).comp (Ideal.Quotient.mk _), fun x hx => Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_map_of_mem _ ((WittVector.mem_span_p_iff_coeff_zero_eq_zero x).2 hx))⟩

theorem res_coeff (m : ℕ) (x : WittVector l k) :
    res l k m (WittVector.constantCoeff x) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

def red (m : ℕ) : Wm l k (m + 1) →+* Wm l k m :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ m.le_succ))

omit [CharP k l] [PerfectRing k l] in
theorem red_mk (m : ℕ) (x : WittVector l k) : red l k m (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (RingHom.id _ x) :=
  Ideal.Quotient.factor_mk _ x

theorem dp_red (m : ℕ) : IsDPMorphism (pd l k (m + 1)) (pd l k m) (red l k m) :=
  RL.pd_mor _ _ _ _ _ _ (RingHom.id _) _ Ideal.Quotient.mk_surjective (pdI_l l (witt_unit l k)) (isPd l k _) (isPd l k _)
    (fun _ hx => hx) fun _ => rfl

variable {k} {O : Type} [CommRing O] (F : B.Fn O) (ρ : O →+* k)

abbrev L (m : ℕ) : (bs l k m).Fun := F.cr (bs l k m) rfl ((res l k m).comp ρ)

abbrev OA (m : ℕ) : Thick (L l F ρ m) ⥤ CommAlgCat.{0} (WittVector l k) := B.OA (L l F ρ m) (Ideal.Quotient.mk _)

abbrev OM (m : ℕ) : Thick (L l F ρ m) ⥤ ModuleCat.{0} (WittVector l k) := B.OM (L l F ρ m) (Ideal.Quotient.mk _)

theorem red_res (m : ℕ) : (Ideal.quotientMap _ (red l k m) (Ideal.map_le_iff_le_comap.1 (dp_red l k m).1)).comp
    ((res l k (m + 1)).comp ρ) = (res l k m).comp ρ := RingHom.ext fun x => by
  obtain ⟨w, hw⟩ := WittVector.constantCoeff_surjective l (ρ x)
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ← hw, res_coeff, res_coeff]; rfl

def redM (m : ℕ) : Mor (L l F ρ (m + 1)) (L l F ρ m) (red l k m) :=
  B.crMor (F := F) (F' := F) (b := bs l k (m + 1)) (b' := bs l k m) (ht := rfl) (ht' := rfl) (red l k m) rfl (dp_red l k m)
    (basePt F _ (red_res l ρ m)) fun _ _ _ => rfl

def redMor (m : ℕ) : CH.Mor (OM l F ρ (m + 1)) (OM l F ρ m) (RingHom.id _) := B.omMor (redM l F ρ m) (RingHom.id _) (red_mk l k m)

def HS (j : ℕ) : Sys.{1} (WittVector l k) where
  M m := CH.H (OM l F ρ m) j
  r m := (redMor l F ρ m).pull j

variable (k) in
abbrev K₀ : Type := FractionRing (WittVector l k)

def D (j : ℕ) : Type 1 := K₀ l k ⊗[WittVector l k] (HS l F ρ j).lim

instance (j : ℕ) : AddCommGroup (D l F ρ j) := inferInstanceAs (AddCommGroup (K₀ l k ⊗[WittVector l k] (HS l F ρ j).lim))

instance (j : ℕ) : Module (K₀ l k) (D l F ρ j) := inferInstanceAs (Module (K₀ l k) (K₀ l k ⊗[WittVector l k] (HS l F ρ j).lim))

end Wc

end CrystallineSemistableComparison
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff =====
