module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

section Lie

variable {R K : Type} [CommRing R] [CommRing K]

def Indep {A : Over (Sp K)} [GrpObj A] {m : ℕ} (x : Fin m → (epsR K ⟶ A)) : Prop :=
  (∀ i, IsTangent (x i)) ∧ ∀ c c' w, IsLieComb c x w → IsLieComb c' x w → c = c'

theorem Indep.of_basis {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {n : ℕ} {e : Fin n → (epsR K ⟶ A)}
    (he : IsLieBasis e) : Indep e :=
  ⟨he.1, fun c _ w h h' => (he.2 w ((LieComb.lieComb_algebra K A n e he.1).2.1 c w h)).unique h h'⟩

theorem Indep.of_eigBasis {O : Type} [CommRing O] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {act : OAct O A}
    {χ : O →+* K} {m : ℕ} {x : Fin m → (epsR K ⟶ A)} (h : EigenvectorLieDegree.IsEigBasis act χ x) : Indep x := by
  refine ⟨fun i => (h.1 i).1, fun c c' w hc hc' => (h.2 w ?_).unique hc hc'⟩
  let y : Fin m → Serre.Lie act := fun i => Serre.Lie.mk act (x i) (h.1 i).1
  have hy : ∀ a i, a • y i = χ a • y i := fun a i => Serre.Lie.ext (Over.OverMorphism.ext ((h.1 i).2 a))
  obtain rfl := (Serre.Lie.isLieComb_iff c y w).1 hc
  refine ⟨Serre.Lie.isTangent _, fun a => ?_⟩
  have : a • ∑ i, c i • y i = χ a • ∑ i, c i • y i := by
    rw [Finset.smul_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm a, hy, smul_comm]
  exact congrArg (fun z : Serre.Lie act => z.hom.left) this

variable {f : R →+* K} {G : Over (Sp R)} [GrpObj G] {A : Over (Sp K)} [GrpObj A] {φ : A.left ⟶ G.left}

end Lie

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] [NumberField k]
  {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)} {𝔭 : HeightOneSpectrum (𝓞 k)}

end Local

end GlobalTheory.FlatDegreeCompare
