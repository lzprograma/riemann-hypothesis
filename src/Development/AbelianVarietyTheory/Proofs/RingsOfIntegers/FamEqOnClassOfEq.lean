module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory

private lemma gs_id_eq_of_presheaf_map_eq {X : Scheme.{0}} {U V : X.Opens} (hle : V ≤ U) {a b : Γ(X, U)} (y : X) (hy : y ∈ V)
    (e : (X.presheaf.map (homOfLE hle).op).hom a = (X.presheaf.map (homOfLE hle).op).hom b) :
    Geo.Tor.gs (𝟙 X) y U a = Geo.Tor.gs (𝟙 X) y U b := by
  rw [← Geo.Tor.gs_res (𝟙 X) y hle hy a, ← Geo.Tor.gs_res (𝟙 X) y hle hy b, e]

theorem fam_eq_on_class_of_eq : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s t : Fam D F k) (α : D.X), (∀ j, (s.s α).f j = (t.s α).f j) →
    ∀ (m : D.X) j, (s.s (α + k • m)).f j = (t.s (α + k • m)).f j := by
  intro hG R _ _ D F _ _ k s t α h m j
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := F) hG k m α
  have Hs := s.fe
  have Ht := t.fe
  unfold DegPre.FamFE at Hs Ht
  have Hs' := Hs m α u hu hc
  have Ht' := Ht m α u hu hc
  unfold GeneratorPullback.SecRel at Hs' Ht'
  refine Geo.Tor.sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  have hcoh : D.P.L.Coh
      (Sum.elim (D.famφ F (α + k • m)) (Sum.elim (fun i => (D.trF F m).left ≫ D.famφ F α i) (D.deltaφ F k α m)))
      (Sum.elim (fun i => J (D.famφ F (α + k • m) i))
        (Sum.elim (fun i => J ((D.trF F m).left ≫ D.famφ F α i)) (fun i => J (D.deltaφ F k α m i)))) := by
    intro a b hab
    rcases a with a | a | a <;> rcases b with b | b | b <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hab ⊢ <;> exact congrArg J hab
  have e := Hs' _ _ _ hcoh
  erw [h, ← Ht' _ _ _ hcoh] at e
  rw [Geo.Tor.sval_of _ _ _ _ (fun i => J (D.famφ F (α + k • m) i)) (fun i => by simp),
    Geo.Tor.sval_of _ _ _ _ (fun i => J (D.famφ F (α + k • m) i)) (fun i => by simp)]
  refine gs_id_eq_of_presheaf_map_eq _ y ?_ e
  simp only [TopologicalSpace.Opens.mem_inf]
  exact ⟨⟨Set.mem_iInter.2 fun i => hJ _, Set.mem_iInter.2 fun i => hJ _⟩, Set.mem_iInter.2 fun i => hJ _⟩

end GlobalTheory
