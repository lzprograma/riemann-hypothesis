module

public import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

namespace GlobalTheory.LiftSys

theorem exists_semilinear_lift_of_projective : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (P : Type) [AddCommGroup P] [Module R₀ P], Module.Projective R₀ P → ∀ (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (W : Submodule R M), (∀ r, π r = 0 → ∀ m ∈ W, r • m = 0) → ∀ (q : M →ₗ[R] M') (v : P →+ M'), (∀ r w, v (π r • w) = r • v w) → (∀ w, ∃ m ∈ W, q m = v w) → ∃ u : P →+ M, (∀ r w, u (π r • w) = r • u w) ∧ (∀ w, u w ∈ W) ∧ ∀ w, q (u w) = v w := by
  intro R R₀ _ _ π hπ P _ _ hP M M' _ _ _ _ W hW q v hv hq
  classical
  choose m hmW hmq using hq
  choose σ hσ using hπ
  have key : ∀ (r s : R) (x : M), x ∈ W → π r = π s → r • x = s • x := by
    intro r s x hx h
    have := hW (r - s) (by rw [map_sub, h, sub_self]) x hx
    rwa [sub_smul, sub_eq_zero] at this
  let f : P → R₀ →+ M := fun w => AddMonoidHom.mk' (fun c => σ c • m w) (by
    intro a b
    rw [← add_smul]
    exact key _ _ _ (hmW w) (by rw [map_add (f := _), hσ, hσ, hσ]))
  have hf : ∀ w c, f w c = σ c • m w := fun _ _ => rfl
  let g : (P →₀ R₀) →+ M := Finsupp.liftAddHom f
  have hg : ∀ w c, g (Finsupp.single w c) = σ c • m w := by
    intro w c
    simp only [g, Finsupp.liftAddHom_apply_single, hf]
  have g1 : ∀ r x, g (π r • x) = r • g x := by
    intro r x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]
    | single w c =>
      rw [Finsupp.smul_single, hg, hg, smul_smul]
      exact key _ _ _ (hmW w) (by rw [map_mul, hσ, hσ, smul_eq_mul])
  have g2 : ∀ x, g x ∈ W := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _)]; exact W.add_mem ha hb
    | single w c => rw [hg]; exact W.smul_mem _ (hmW w)
  have g3 : ∀ x, q (g x) = v (Finsupp.linearCombination R₀ id x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | single w c =>
      rw [hg, Finsupp.linearCombination_single, map_smul, hmq, ← hv, hσ]
      rfl
  obtain ⟨s, hs⟩ := hP.out
  refine ⟨g.comp s.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro r w
    show g (s (π r • w)) = r • g (s w)
    rw [map_smul, g1]
  · intro w
    exact g2 _
  · intro w
    show q (g (s w)) = v w
    rw [g3, hs]

end GlobalTheory.LiftSys
