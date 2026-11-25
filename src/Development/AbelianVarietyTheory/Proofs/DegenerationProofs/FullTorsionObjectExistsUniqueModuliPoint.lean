module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex

theorem GlobalTheory.FullPoint.fullAt_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {K : Type} [Field K] (y : Sp K ⟶ Xo.XF c) (o : Full D K) :
    FullAt Y y o ↔ FullPoint.IsFibre Y.oF y o ∧ ∀ f : KA l →+* K, y ≫ pullback.fst _ _ ≫ Xo.s = spMap f →
      o.ρ = f (baseKA l).ρ ∧ (o.I.ζ l.A : K) = f (baseKA l).ζ :=
  ⟨fun ⟨φ, a, b, c, d, e, f⟩ => ⟨⟨φ, a, b, c, d, e⟩, f⟩, fun ⟨⟨φ, a, b, c, d, e⟩, f⟩ => ⟨φ, a, b, c, d, e, f⟩⟩

theorem GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] (bF : c.F →+* K), (∀ o : Full D K, (∀ r : c.F, (r : ℂ) = H.rt0 → o.ρ = bF r) → (∀ z : c.F, (z : ℂ) = zeta l.A → (o.I.ζ l.A : K) = bF z) → ∃! y : Sp K ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap bF ∧ FullAt Y y o) ∧ (∀ y : Sp K ⟶ Xo.XF c, ∃ o, FullAt Y y o) ∧ ∀ (K' : Type) [Field K'] (f : K →+* K') y o o', FullAt Y y o → FullExt f o o' → FullAt Y (spMap f ≫ y) o' := by
  intro hv _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y K _ _ bF
  refine ⟨fun o hρ hζ => ?_, fun y => ?_, fun K' _ f y o o' h h' => ?_⟩
  · obtain ⟨y, ⟨h₁, h₂⟩, hu⟩ := FullPoint.existsUnique_point hv.1.1 Y bF o hρ hζ
    refine ⟨y, ⟨h₁, (FullPoint.fullAt_iff Y y o).2 ⟨h₂, fun f hf => ?_⟩⟩,
      fun y' h => hu y' ⟨h.1, ((FullPoint.fullAt_iff Y y' o).1 h.2).1⟩⟩
    rw [pullback.condition, ← Category.assoc, h₁, ← spMap_comp] at hf
    obtain rfl := FullPoint.spMap_inj hf
    exact ⟨hρ _ rfl, hζ _ rfl⟩
  · obtain ⟨o, h⟩ := FullPoint.exists_isFibre Y.oF y
    exact ⟨o, (FullPoint.fullAt_iff Y y o).2 h⟩
  · obtain ⟨hρ, hζ, ψ, g₁, g₂, g₃, g₄⟩ := h'
    obtain ⟨h₁, h₂⟩ := (FullPoint.fullAt_iff Y y o).1 h
    refine (FullPoint.fullAt_iff Y _ o').2 ⟨FullPoint.IsFibre.ext f h₁ ψ g₁ g₂ g₃ g₄, fun g hg => ?_⟩
    obtain ⟨j, hj⟩ : ∃ j : KA l →+* K, y ≫ pullback.fst _ _ ≫ Xo.s = spMap j :=
      ⟨(Spec.preimage (y ≫ pullback.fst _ _ ≫ Xo.s)).hom, (Spec.map_preimage _).symm⟩
    rw [Category.assoc, hj, ← spMap_comp] at hg
    obtain rfl := FullPoint.spMap_inj hg
    rw [hρ, hζ _ l.A_pos, (h₂ j hj).1, (h₂ j hj).2]
    exact ⟨rfl, rfl⟩
