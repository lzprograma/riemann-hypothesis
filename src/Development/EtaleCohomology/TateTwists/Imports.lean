module

public import Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationExistsOfEvalua
public import Development.EtaleCohomology.TateTwists.PpEvBasicPf
public import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalDifferentialFormulaHolds
public import Development.EtaleCohomology.TateTwists.PpEvMkPf
public import Development.EtaleCohomology.TateTwists.EtaleCochainSemilinearMapCompCompatible
public import Development.EtaleCohomology.TateTwists.EtaleCochainSemilinearMapOnClasses
import Mathlib.Tactic.Linter.Style

section
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSemilinearCohomologyOperationImageSpec : Prop :=
  ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
    (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
    ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β

namespace OpCompPf

theorem ev_comp_ofHom {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

noncomputable def invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) : SemiMap J I where
  app U s := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm.toAddMonoidHom
  nat {V U} g s a := by
    apply (hb V s).1
    have h1 := ρ.nat g s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app V s ((AddEquiv.ofBijective (ρ.app V s) (hb V s)).symm (Sec.res g a)) = Sec.res g a :=
      (AddEquiv.ofBijective (ρ.app V s) (hb V s)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [h3, ← h1, h2]
  comm U s t a := by
    apply (hb U t).1
    have h1 := ρ.comm U s t ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app U t ((AddEquiv.ofBijective (ρ.app U t) (hb U t)).symm (Sec.map (J.d s t) a)) = Sec.map (J.d s t) a :=
      (AddEquiv.ofBijective (ρ.app U t) (hb U t)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [h3, ← h1, h2]

theorem invMap_app {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (J.X s) U) :
    ρ.app U s ((invMap ρ hb).app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a

theorem app_invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (invMap ρ hb).app U s (ρ.app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm_apply_apply a

end OpCompPf

open OpCompPf in
theorem etale_cohomology_operation_comp_of_image_spec (hspec : EtaleSemilinearCohomologyOperationImageSpec) : EtaleCochainSemilinearMapCompCompatible := by
  intro S R _ _ I J J' ρ ρ' u hu
  constructor
  · intro E n x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
    rw [(hspec S R ρ).2 E n α β hβ, cpost_mk]
    apply (hspec S R ρ').2
    intro p s h U y
    show ev (β.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y = _
    rw [ev_comp_ofHom, hβ p s h U y, hu]
  · intro hb E n
    let σ := invMap ρ hb
    rw [Function.bijective_iff_has_inverse]
    refine ⟨σ.op.app E n, ?_, ?_⟩
    · intro x
      obtain ⟨α, rfl⟩ := x.mk_surjective
      obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
      rw [(hspec S R ρ).2 E n α β hβ]
      apply (hspec R S σ).2
      intro p s h U y
      rw [hβ p s h U y]
      exact (app_invMap ρ hb U s _).symm
    · intro x
      obtain ⟨β, rfl⟩ := x.mk_surjective
      obtain ⟨γ, hγ⟩ := (hspec R S σ).1 E n β
      rw [(hspec R S σ).2 E n β γ hγ]
      apply (hspec S R ρ).2
      intro p s h U y
      rw [hγ p s h U y]
      exact (invMap_app ρ hb U s _).symm

end LateralTheory.EtaleFoundations
end
end


-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.TateTwists.EtaleCohomologyEvaluationConnectingHom, Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationImageSpecOfHyp, Development.EtaleCohomology.TateTwists.Imports

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleCohomologyEvaluationConnectingHom =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleCohomologyEvaluationConnectingHom", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationExistsOfEvalua\npublic import Development.EtaleCohomology.TateTwists.PpEvBasicPf\npublic import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalDifferentialFormulaHolds\npublic import Development.EtaleCohomology.TateTwists.PpEvMkPf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

namespace LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
alias etale_evaluation_map_basic_of_components := _root_.LateralTheory.EtaleFoundations.pp_ev_basic_of
alias etale_cohomology_evaluation_mk := _root_.LateralTheory.EtaleFoundations.pp_ev_mk_of
theorem etale_cohomology_evaluation_connecting_hom : LateralTheory.EtaleFoundations.pp_ev_delta :=
  LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds
theorem etale_torsion_cohomology_operation_spec : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  apply LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation <;> first | exact etale_evaluation_map_basic_of_components | exact etale_cohomology_evaluation_mk | exact etale_cohomology_evaluation_connecting_hom
alias intersectionNumber_baseChange := _root_.LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses.etale_torsion_cohomology_operation_spec
end LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleCohomologyEvaluationConnectingHom =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationImageSpecOfHyp =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationImageSpecOfHyp", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtaleCohomologyOperationCompOfImageSpec\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_semilinear_cohomology_operation_image_spec_of_hyp
    (hImage₂ : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
      (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
      ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
        ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β) :
    EtaleSemilinearCohomologyOperationImageSpec :=
  hImage₂

end LateralTheory.EtaleFoundations
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationImageSpecOfHyp =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.Imports =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.Imports", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtaleCochainSemilinearMapCompCompatible\npublic import Development.EtaleCohomology.TateTwists.EtaleCohomologyEvaluationConnectingHom\npublic import Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationImageSpecOfHyp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.EtaleCohomology.TateTwists.EtaleCochainSemilinearMapOnClasses\npublic import Development.EtaleCohomology.TateTwists.EtaleCohomologyOperationCompOfImageSpec\n\n"}
section -- clump:auto
@[expose] public section

theorem LateralTheory.Fix.EtaleCochainSemilinearMapCompCompatible.intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible :=
  LateralTheory.EtaleFoundations.etale_cohomology_operation_comp_of_image_spec
    (LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_image_spec_of_hyp (by
      have h := LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses.intersectionNumber_baseChange
      unfold LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses at h
      exact h))
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.Imports =====
