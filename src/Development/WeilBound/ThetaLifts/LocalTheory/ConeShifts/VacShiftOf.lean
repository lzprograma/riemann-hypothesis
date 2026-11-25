module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.MCSpan
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PureIte
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdeleCongruenceUnitCriterion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FinStmt
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FubMain
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.IdealId0
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.KAtCompact
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ExtendByZeroOnSubsetApplyCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ConeFactorisationOfCodimensionTwo, Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FinSpan, Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.VacShiftOf

-- ===== clump member: Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ConeFactorisationOfCodimensionTwo =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ConeFactorisationOfCodimensionTwo", "h": "module\n\npublic import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PureIte\npublic import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation\npublic import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical\npublic import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem unr_div {χ χ' : Chr F E} {S : Set (Pl F)} (h : UnrOff χ S) (h' : UnrOff χ' S) : UnrOff (χ / χ') S := fun w hw x hx => by
  have a := h w hw x hx
  have b := h' w hw x hx
  have : locChar (χ / χ') w x = locChar χ w x / locChar χ' w x := map_div Circle.toUnits _ _
  rw [this, a, b, div_one]

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem nu_cont (t : IsTriple B G X om om') : Continuous X.ν := (isHecke_div t.chars.heckeα t.chars.heckeβ).1

theorem nu_res (t : IsTriple B G X om om') : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.ν 0 := fun x => by
  have h := resEtaPow_div t.chars.resα t.chars.resβ x
  rw [(add_comm a a' ▸ t.geo.even : Even (a' + a)).neg_one_pow] at h
  rw [pow_zero]
  exact h

theorem coneIntegralFactorisation_of (hA : ActsEx) (hI : IdeleFub) (hKF : KFub) (hV : VacFixX) (hS : VacShift) (hAr : ArchCone) (hF : FinM)
    (hP : PureFac) (hSp : SchSpan) (hId : IdealM) : PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation := by
  obtain ⟨a₁, a₂, b₁, b₂, hId⟩ := hId
  refine ⟨a₁, a₂, ?_⟩
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' c e ei ev he hE K μK μ m hK h1 h2 hm
  by_cases ex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' t t₁ => (ex ⟨X, om, om', om₁, om₁', t, t₁⟩).elim⟩
  obtain ⟨X₀, o, o', o₁, o₁', t₀, t₀₁⟩ := ex
  have hC : Cfg B G.M G₁.M H H' e (shiftA H H') :=
    ⟨t₀.base, ⟨_, _, t₀.geo.hV⟩, ⟨_, _, t₀.geo.hW⟩, ⟨_, _, t₀₁.geo.hV⟩, ⟨_, _, t₀₁.geo.hW⟩, t₀.geo.hM, t₀₁.geo.hM,
      ⟨_, _, c.hH⟩, ⟨_, _, c.hH'⟩, .inl ⟨he, rfl⟩⟩
  obtain ⟨𝔞, h0, hlat, hcnt, hval⟩ := hId F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ _ _ _ _ t₀.base t₀.geo.hV t₀.geo.hW c.hH c.hH'
    (by omega) (by omega) (by omega) (by omega) _ _ _ (.inl ⟨rfl, rfl, rfl⟩)
  have hz : 2 ≤ (b + 2 - a') / 2 := by
    have := t₀.geo.eBig
    omega
  obtain ⟨κ, hκ, HG⟩ := gen hA hI hKF hV hS hAr hF hP hSp hC hE hK h1 h2 hm h0 hlat hz
  refine ⟨κ, hκ, fun X om om' om₁ om₁' t _ => ?_⟩
  have := HG _ _ _ _ _ _ _ (by
    refine ⟨t.base, t.geo.hV, t.geo.hW, t.geo.hM, t.chars.heckeβ, ?_, t.chars.resβ, ?_, t.weil⟩
    · exact ⟨t.chars.heckeβ.1.div' t.chars.heckeα.1, fun x => by rw [MonoidHom.div_apply, t.chars.heckeβ.2, t.chars.heckeα.2, div_one]⟩
    · intro x
      rw [MonoidHom.div_apply, Circle.coe_div, t.chars.resβ, t.chars.resα]
      split_ifs <;> simp [pow_add, div_eq_mul_inv, ← inv_pow, mul_comm]) X.ν X.S₀ X.T (nu_cont t) (by classical exact Finset.subset_union_left)
    (unr_div t.chars.unrα t.chars.unrβ) t.chars.unrβ (unr_div t.chars.unrβ t.chars.unrα)
    fun w hw => ⟨t.chars.ram w hw, hcnt w (t.chars.sub hw)⟩
  rw [hval X.ν (nu_cont t) (nu_res t) fun w hw => unr_div t.chars.unrα t.chars.unrβ w fun h => hw (t.chars.sub h)] at this
  exact this

theorem coneFacB_of (hA : ActsEx) (hI : IdeleFub) (hKF : KFub) (hV : VacFixX) (hS : VacShift) (hAr : ArchCone) (hF : FinM)
    (hP : PureFac) (hSp : SchSpan) (hId : IdealM) : ConeFacB := by
  obtain ⟨a₁, a₂, b₁, b₂, hId⟩ := hId
  refine ⟨b₁, b₂, ?_⟩
  intro F E _ _ _ _ _ σ B a b G G₁ H H' c e ei ev he hE K μK μ m hK h1 h2 hm
  by_cases ex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' t t₁ => (ex ⟨X, om, om', om₁, om₁', t, t₁⟩).elim⟩
  obtain ⟨X₀, o, o', o₁, o₁', t₀, t₀₁⟩ := ex
  have hC : Cfg B G.M' G₁.M' H H' e (shiftB σ H H') :=
    ⟨t₀.base, ⟨_, _, t₀.geo.hV'⟩, ⟨_, _, t₀.geo.hW⟩, ⟨_, _, t₀₁.geo.hV'⟩, ⟨_, _, t₀₁.geo.hW⟩, t₀.geo.hM', t₀₁.geo.hM',
      ⟨_, _, c.hH⟩, ⟨_, _, c.hH'⟩, .inr ⟨he, rfl⟩⟩
  obtain ⟨𝔞, h0, hlat, hcnt, hval⟩ := hId F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ _ _ _ _ t₀.base t₀.geo.hV' t₀.geo.hW c.hH c.hH'
    (by omega) (by omega) (by omega) (by omega) _ _ _ (.inr ⟨rfl, rfl, rfl⟩)
  have hz : 2 ≤ (a - (b + 2)) / 2 + 1 := by
    have := t₀.geo.eBig
    omega
  obtain ⟨κ, hκ, HG⟩ := gen hA hI hKF hV hS hAr hF hP hSp hC hE hK h1 h2 hm h0 hlat hz
  refine ⟨κ, hκ, fun X om om' om₁ om₁' t _ => ?_⟩
  have := HG _ _ _ _ _ _ _ (by
    refine ⟨t.base, t.geo.hV', t.geo.hW, t.geo.hM', t.chars.heckeα, ?_, t.chars.resα, ?_, t.weil'⟩
    · exact ⟨t.chars.heckeα.1.div' t.chars.heckeβ.1, fun x => by rw [MonoidHom.div_apply, t.chars.heckeα.2, t.chars.heckeβ.2, div_one]⟩
    · intro x
      rw [MonoidHom.div_apply, Circle.coe_div, t.chars.resα, t.chars.resβ]
      split_ifs <;> simp [pow_add, div_eq_mul_inv, ← inv_pow, mul_comm]) X.ν X.S₀ X.T (nu_cont t) (by classical exact Finset.subset_union_left)
    (unr_div t.chars.unrα t.chars.unrβ) t.chars.unrα (unr_div t.chars.unrα t.chars.unrβ)
    fun w hw => ⟨t.chars.ram w hw, hcnt w (t.chars.sub hw)⟩
  rw [hval X.ν (nu_cont t) (nu_res t) fun w hw => unr_div t.chars.unrα t.chars.unrβ w fun h => hw (t.chars.sub h)] at this
  exact this

theorem coneFactorisation_of_codimension_two (h : PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation) : ConeFacA := by
  obtain ⟨e₁, e₂, h⟩ := h
  exact ⟨e₁, e₂, fun F E _ _ _ _ _ σ B b a' G G₁ H H' c => h F E σ B b a' G G₁ H H' ⟨c.eV, c.q1.trans c.q0.symm, c.ep, c.hH, c.hH'⟩⟩

end PositivityTheory.ThKG.Loc.Cone

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ConeFactorisationOfCodimensionTwo =====

-- ===== clump member: Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FinSpan =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FinSpan", "h": "module\n\npublic import Development.WeilBound.ThetaLifts.LeviDeterminants.MCSpan\npublic import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone\npublic import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdeleCongruenceUnitCriterion\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Connected.Separation\nimport Mathlib.Topology.MetricSpace.Ultra.TotallySeparated\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Fin

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac
open GlobalTheory.Doubling (absE)

theorem schSpan : SchSpan := by
  intro F _ _ κ _ vac hSB hstd
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    obtain ⟨m, c, φ, h1, h2, rfl⟩ := PositivityTheory.ThKF0.Span.exists_sum_finprod hg
    have e : pureA F f (∑ k, c k • fun y => ∏ᶠ v, φ k v fun i => evalV F v (y i)) = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
      funext x
      simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
      exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
    rw [e]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    have hf : {v | ¬ φ k v = vac v}.Finite := by
      refine eventually_cofinite.1 ?_
      filter_upwards [h2 k, hstd] with v a b using a.trans b.symm
    exact ⟨f, φ k, hf.toFinset, h1 k, fun v hv => by simpa using hv, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, φ, T, h1, h2, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ h1 ?_
    filter_upwards [T.eventually_cofinite_notMem, hstd] with v a b using (h2 v a).trans b

end PositivityTheory.ThKG.Loc.Cone.Fin

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FinSpan =====

-- ===== clump member: Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.VacShiftOf =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.VacShiftOf", "h": "module\n\npublic import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation\npublic import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FinStmt\npublic import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PureIte\npublic import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical\npublic import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ConeFactorisationOfCodimensionTwo\npublic import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FinSpan\npublic import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FubMain\npublic import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.IdealId0\npublic import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.KAtCompact\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\npublic import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ExtendByZeroOnSubsetApplyCoe\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF

theorem vacShift_of (h : FinCone2) : VacShift := fun F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v =>
  (h F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v).1

theorem finM_of (h : FinCone2) : FinM := fun F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v =>
  (h F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v).2.2

theorem coneFac_all (hA : ActsEx) (hSt : StabEx) (hO : ArchOp) (hU : ArchUniq) (hPS : PositivityTheory.Mix.PureSt) (hAr : ArchCone) (v : VacFixX) :
    PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation ∧ ConeFacA ∧ ConeFacB := by
  have f := Fin.finCone2_of ideleFub Id.idealId0 hSt
  have p := pureFac_of hA hO hU v (vacShift_of f) hPS
  have a := coneIntegralFactorisation_of hA ideleFub (kFub_of hSt) v (vacShift_of f) hAr (finM_of f) p Fin.schSpan Id.idealId'
  exact ⟨a, coneFactorisation_of_codimension_two a, coneFacB_of hA ideleFub (kFub_of hSt) v (vacShift_of f) hAr (finM_of f) p Fin.schSpan Id.idealId'⟩

end PositivityTheory.ThKG.Loc.Cone

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.VacShiftOf =====
