module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericLieMultiplicitiesUniformisedGroup
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEqSmulOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.CharRank

open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.Serre GlobalTheory.EigenSplit Matrix GlobalTheory.LieUnif
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)
open scoped CategoryTheory.Obj

theorem lieMult_unif_loc {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] (f : R →+* F) (hf : Function.Injective f)
    (τ : 𝓞 E →+* F) (N : ℕ) (hN : LieMult t.act (spMap f) τ N) :
    letI := H.starRing; ∃ n, LieMult (ofRingAct P.oD.onB.toRingAct) (spMap f) τ n ∧
      n + Module.finrank (𝓞 E) P.D.toPre.X = N := by
  classical
  letI := H.starRing
  haveI : CharZero F := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  have := P.U.smooth
  have : Smooth P.D.toPre.P.A.hom := P.D.toPre.P.smoothDim.smooth
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis t.G P.U.smooth
  obtain ⟨ρ, hρ⟩ := LieEigen.exists_action hv t.act
  obtain ⟨h, w, hw⟩ := Chart.exists_isLieBasis P.D.toPre.P.A this
  obtain ⟨ρB, hρB⟩ := LieEigen.exists_action hw (ofRingAct P.oD.onB.toRingAct)
  let b := Module.finBasis ℤ P.D.toPre.X
  have htr := trace_of_unif P.U.toUnifPre P.lin hv hρ hw hρB b
  obtain ⟨v', ρ', hv', hρ', hM⟩ := ToricRank.exists_action_pullback hv hρ f
  obtain ⟨w', ρB', hw', hρB', hMB⟩ := ToricRank.exists_action_pullback hw hρB f
  let aG := t.act.pullback (spMap f) t.G
  let aB := (ofRingAct P.oD.onB.toRingAct).pullback (spMap f) P.D.toPre.P.A
  haveI := Module.Finite.of_basis (Lie.basis aG hv')
  haveI := Module.Finite.of_basis (Lie.basis aB hw')
  have tG : ∀ a, LinearMap.trace F (Lie aG) (Module.toModuleEnd F (Lie aG) a) = f (LinearMap.trace R _ (ρ a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hv' aG a _ (fun c => by rw [← hM, hρ'])
  have tB : ∀ a, LinearMap.trace F (Lie aB) (Module.toModuleEnd F (Lie aB) a) = f (LinearMap.trace R _ (ρB a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hw' aB a _ (fun c => by rw [← hMB, hρB'])
  let σ : (E →+* F) → 𝓞 E →+* F := fun i => i.comp (algebraMap (𝓞 E) E)
  have hinj : Function.Injective σ := fun i j hij =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) hij
  have hσ : IsSplitting σ := by
    simpa using isSplitting_of_isDomain hinj (NumberField.Embeddings.card E F) (RingHom.id F)
      (isUnit_discr_of_charZero F)
  obtain ⟨j, rfl⟩ : ∃ j, σ j = τ :=
    ⟨IsFractionRing.lift (injective_of_charZero τ), RingHom.ext fun x => IsFractionRing.lift_algebraMap (injective_of_charZero τ) x⟩
  have : Module.Finite (𝓞 E) P.D.toPre.X := .of_restrictScalars_finite ℤ _ _
  have he : ∀ {X : Over (Sp F)} [GrpObj X] [IsCommMonObj X] (a : OAct (𝓞 E) X),
      Lie.eig a (σ j) = eigenSub (Module.toModuleEnd F (Lie a)) (σ j) := fun a =>
    Submodule.ext fun v => by rw [mem_eigenSub]; rfl
  have hm := mult_eq hinj (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aG)) (σ i)))
    (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aB)) (σ i)))
    (Module.finrank (𝓞 E) P.D.toPre.X) (fun a => by
      have hT := trace_eq_sum hσ (torusRep (𝓞 E) P.D.toPre.X F) a
      simp only [fun i => finrank_eigenSub_torusRep (X := P.D.toPre.X) (σ i) (injective_of_charZero _)] at hT
      rw [← trace_eq_sum hσ, ← trace_eq_sum hσ, ← hT, tG, tB, htr, trace_torusRep b, map_add (f := _), map_intCast]) j
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he] at hN
  refine ⟨_, ?_, hm.symm.trans hN.2⟩
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he]
  exact ⟨inferInstance, rfl⟩

alias bar_rt_neg := _root_.GlobalTheory.HostModel.bar_rt

theorem exists_chars {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [IsAlgClosed K] [CharZero K] (δ : K) (hδ : δ ^ 2 = -(H.d : K)) :
    ∃ τ₁ τ₂ : 𝓞 E →+* K, τ₁ H.rt = δ ∧ τ₂ H.rt ≠ δ := by
  let e₀ : E →ₐ[ℚ] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let τ₀ : 𝓞 E →+* K := e₀.toRingHom.comp (algebraMap (𝓞 E) E)
  let τ' : 𝓞 E →+* K := τ₀.comp (H.bar : 𝓞 E →+* 𝓞 E)
  have h' : τ' H.rt = -τ₀ H.rt := by
    change τ₀ (H.bar H.rt) = _
    rw [bar_rt_neg, map_neg]
  have h0 : (τ₀ H.rt) ^ 2 = δ ^ 2 := by rw [← map_pow, H.rt_sq, map_neg, map_natCast, hδ]
  have hne : δ ≠ -δ := fun h => by
    have h2 : δ = 0 := by
      have : (2 : K) * δ = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    rw [h2] at hδ
    have : (H.d : K) = 0 := by linear_combination hδ
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h0 with h | h
  · exact ⟨τ₀, τ', h, by rw [h', h]; exact fun e => hne e.symm⟩
  · exact ⟨τ', τ₀, by rw [h', h, neg_neg], by rw [h]; exact fun e => hne e.symm⟩

end GlobalTheory.CharRank
