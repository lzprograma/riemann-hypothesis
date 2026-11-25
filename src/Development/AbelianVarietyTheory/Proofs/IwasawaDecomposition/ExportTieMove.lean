module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBasisAtTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarMulSelfOfPair
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyAll
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepsMatHeqRefl
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
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatCopyIff, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtremalVectorMemLowestKType, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTieMoveOfPin, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExtremalVectorOfRealSideBaseChange, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingRelationTransferIdentity, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClassSystem, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupRelIffSameData, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupMove, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSetupOverExtendedDataIntegralFormsEq, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieMove, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpTiedCopy, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsScalarScale, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExportTieMove

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatCopyIff =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatCopyIff", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBasisAtTransport\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

namespace GlobalTheory.TwInputs.Move.RatUp

variable {D : D7} (r : Rest D)

theorem placeMap_up {S T : HSp D} (B : Base S T) (a : AE D) :
    HEq ((baseUp r B).F.placeMap ((a))) (B.F.placeMap a) := by
  have h : (fun Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) =>
      (IsPlaceModel (baseUp r B).F.ψ (symplO _ _) (heisO (baseUp r B).F.ψ _ _) ((by exact (a :))) (baseUp r B).F.lat 1 (baseUp r B).F.f₀
        ((by exact (Tm :))))) = IsPlaceModel B.F.ψ (symplO S T) (heisO B.F.ψ S T) a B.F.lat 1 B.F.f₀ :=
    funext fun Tm => propext ⟨fun g => ⟨(by exact (g.1 :)), (by exact (g.2 :)), (by exact (g.3 :))⟩, fun g => ⟨(by exact (g.1 :)), (by exact (g.2 :)), (by exact (g.3 :))⟩⟩
  delta Frame.placeMap
  exact heq_of_eq (congrArg Classical.epsilon h)

open Classical in
theorem vecAt_up {S T : HSp D} (B : Base S T) : (baseUp r B).vecAt = (B.vecAt) := by
  delta ExportSeries.Base.vecAt Frame.vec
  rewrite [show (baseUp r B).F.placeMap = ((by exact (B.F.placeMap :))) from (by exact ((funext fun a => eq_of_heq (placeMap_up r B a)) :))]
  dsimp only [halfIdem, Frame.datumFn, ExportSeries.Base.locFn, baseUp, twistUp]
  rfl

private theorem series_up {S T : HSp D} (B : Base S T) :
    @series (overD D r) S T (baseUp r B).F = @series D S T B.F := by
  funext ω f g
  refine LinearMap.ext fun P => funext fun x => ?_
  delta series thetaKO
  refine congrArg (fun v : WO S T → ℂ => ω (g, x) v 0) ?_
  dsimp only [Frame.fock, pureTensorO, aPlusAll, aPlus, crea, Datum.dRho, baseUp]
  rfl

theorem theta_up {S T : HSp D} (B : Base S T) : (baseUp r B).theta = (B.theta) := by
  delta ExportSeries.Base.theta ExportSeries.Base.vecBase
  rewrite [vecAt_up r B, series_up r B]
  rfl

theorem genSet_up {S T : HSp D} (B : Base S T) (ω) (t : Twist D Circle) :
    (baseUp r B).genSet (((ω : PairRep S T))) (twistUp r t) = ((B.genSet ω t : GA (overD D r) S → PolF (overD D r) T.rank S.rank → Set (GA (overD D r) T → ℂ))) := by
  delta ExportSeries.Base.genSet ExportSeries.Base.gen ExportSeries.Base.vecFlat
  rewrite [vecAt_up r B, series_up r B]
  rfl

def univUp {A : Type} [AddCommGroup A] (t : UnivTwist D A) : UnivTwist (overD D r) A := ⟨(by exact (t.del :)), (by exact (t.kap :))⟩

theorem xiCoef_up {S T : HSp D} {A : Type} [AddCommGroup A] [Fintype A] (B : Base S T) (ω) (u : UnivTwist D A) :
    (baseUp r B).xiCoef (((ω : PairRep S T))) (univUp r u) = ((B.xiCoef ω u : (Q : Finset (Pl (overD D r).host.E)) → ((PP : Pl (overD D r).host.E) → A → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) → GA (overD D r) S → PolF (overD D r) T.rank S.rank → (↥Q → A) → GA (overD D r) T → ℂ)) := by
  delta ExportSeries.Base.xiCoef ExportSeries.Base.xi ExportSeries.Base.vecFam
  rewrite [vecAt_up r B, series_up r B]
  rfl

section Lat

variable {r} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (h : CopyTw D (overD D r) ι e)
include h

theorem embLL0_up : embLL0 (overD D r) = (embLL0 D).comp e.toRingHom := RingHom.ext fun x => (h.embLL0_eq x).symm

theorem labLL0_up (τ : D.what₂.Tau) : e.toRingHom.comp (labLL0 (overD D r) ((τ))) = (labLL0 D τ) := by
  refine RingHom.ext fun x => (embLL0 D).injective ((h.embLL0_eq _).trans ?_)
  have a := DFunLike.congr_fun (embLL0_labLL0 (D := overD D r) ((by exact (τ :)))) x
  have c := DFunLike.congr_fun (embLL0_labLL0 (D := D) τ) ((by exact (x :)))
  refine Eq.trans a ?_
  exact (by exact (c.symm :))

theorem coefLat_up {S T : HSp D} (B : Base S T) (O : Subring ℂ) (g : Bridge.Gf S) :
    (baseUp r B).coefLat (embLL0 (overD D r)) (labLL0 (overD D r)) O ((g)) = (B.coefLat (embLL0 D) (labLL0 D) O g) := by
  have a := GlobalTheory.CoefLatIso.coefLatFn_ringEquiv D S.rank _ _ e (embLL0 D) ((by exact ((labLL0 (overD D r)) :))) O B.w.lam (B.latAt g)
  have c : (fun τ : D.what₂.Tau => e.toRingHom.comp (((by exact ((labLL0 (overD D r)) :)) : D.what₂.Tau → (D.host.E →+* ↥(overD D r).LL0)) τ)) =
      labLL0 D := funext fun τ => (by exact ((labLL0_up h τ) :))
  rw [← embLL0_up h, c] at a
  exact (by exact ((congrArg (fun L : Submodule O (GLR D S.rank → ℂ) => (harm T.rank B.w B.F.BS).restrictScalars O ⊓
    L.comap ((harmFn T.rank B.w B.F.BS).restrictScalars O)) a) :))

end Lat

section Setup

variable (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem se_theta : (setupUp r ρ).theta ((i)) ((j)) b = (ρ.theta i j b) := by
  funext h P
  have e : @Eq (type_of% (ρ.B i j b).theta) ((by exact ((baseUp r (ρ.B i j b)).theta :))) (ρ.B i j b).theta :=
    (by exact ((theta_up r (ρ.B i j b)) :))
  exact (by exact ((congrArg (fun t : type_of% (ρ.B i j b).theta => t (ρ.om i j b 1) ((by exact (h :))) ((by exact (P :)))) e) :))

theorem se_gens : (setupUp r ρ).gens ((i)) ((j)) b = (ρ.gens i j b) := by
  funext k Q ψ
  exact (by exact ((genSet_up r (ρ.B i j b) (ρ.om i j b 1) (ρ.tw i b k ((by exact (Q :))) ((by exact (ψ :))))) :))

private theorem univOf_up (Q : Finset (Pl D.host.E)) (M : ℕ) :
    univOf (overD D r).nexp i Q M (setupUp r ρ).rc =
      univUp r (univOf D.nexp i Q M ρ.rc) := by
  dsimp only [setupUp, univOf, univUp, coord, Recip.pull, Recip.sym, resOf, IsResAt]
  rfl

theorem se_xi : (setupUp r ρ).xi ((i)) ((j)) b (overD D r).nexp = (ρ.xi i j b D.nexp) := by
  funext Q M
  let Q₀ := admissibleConjugatePairPlaces (overD D r).ntw i Q M
  let u := univOf D.nexp i Q₀ M ρ.rc
  let ω := ρ.om i j b 1
  let Φ := ExportSeries.Base.univFam u (ρ.β j)
  have atFam := congrArg
    (fun F : type_of% ((ρ.B i j b).xiCoef ω u) => F (half (ρ.ch i) Q₀) Φ)
    (xiCoef_up r (ρ.B i j b) ω u)
  delta Setup.xi
  rewrite [univOf_up r ρ i Q₀ M]
  dsimp only [setupUp, ω, Φ, u, Q₀, univUp, ExportSeries.Base.univFam,
    admissibleConjugatePairPlaces, Formalism.MainNotions.NAdm.AdmQ,
    Formalism.MainNotions.NAdm.TWSet] at atFam ⊢
  exact atFam

variable {r ρ i j b} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (h : CopyTw D (overD D r) ι e)
include h

theorem se_lat (O : Subring ℂ) (g : GA D (Vc D j)) : (setupUp r ρ).lat ((i)) ((j)) b O ((g)) = (ρ.lat i j b O g) :=
  (by exact ((coefLat_up h (ρ.B i j b) O (finPt _ g)) :))

theorem datum_up {s g P} (d : ρ.IsDatum i j b s g P) : (setupUp r ρ).IsDatum ((i)) ((j)) b ((s)) ((g)) ((P)) :=
  ⟨(by exact (d.split :)), (by exact (d.off :)), (by exact (d.fin :)), (by exact (d.supp :)), by
    have a := se_lat (ρ := ρ) (i := i) (j := j) (b := b) h (ρ.eO i b).range g
    have c := (le_of_eq a.symm) ((by exact (d.mem :)) : ((by exact (P :))) ∈ _)
    exact (by exact (c :))⟩

theorem datum_dn {s g P} (d : (setupUp r ρ).IsDatum ((i)) ((j)) b s g P) : ρ.IsDatum i j b ((s)) ((g)) ((P)) :=
  ⟨(by exact (d.split :)), (by exact (d.off :)), (by exact (d.fin :)), (by exact (d.supp :)), by
    have a := se_lat (ρ := ρ) (i := i) (j := j) (b := b) h (ρ.eO i b).range ((by exact (g :)))
    have c := (le_of_eq a) ((by exact (d.mem :)) : ((by exact (P :))) ∈ _)
    exact (by exact (c :))⟩

omit h in
variable (r) in
def rdUp (rd : Rd ρ D.nexp i j b) : Rd (setupUp r ρ) (overD D r).nexp ((i)) ((j)) b := (rd)

theorem rat_up {hρ : ρ.Good} {hρ' : (setupUp r ρ).Good} {rd : Rd ρ D.nexp i j b} (g : SeriesTie.Rat hρ rd) :
    SeriesTie.Rat hρ' (rdUp r rd) := by
  refine ⟨fun s x P d => ?_, fun k Q ψ h1 h2 s x P d => ?_, fun Q M h1 s x P d h2 a => ?_⟩
  · rewrite [se_theta r ρ i j b]
    exact (by exact ((g.1 _ _ _ (datum_dn h d)) :))
  · rewrite [se_gens r ρ i j b]
    exact (by exact ((g.2.1 k ((by exact (Q :))) ((by exact (ψ :))) ((by exact (h1 :))) ((by exact (h2 :))) _ _ _ (datum_dn h d)) :))
  · rewrite [se_xi r ρ i j b]
    exact (by exact ((g.2.2 ((by exact (Q :))) M ((by exact (h1 :))) _ _ _ (datum_dn h d) ((by exact (h2 :))) ((by exact (a :)))) :))

theorem rat_dn {hρ : ρ.Good} {hρ' : (setupUp r ρ).Good} {rd : Rd ρ D.nexp i j b} (g : SeriesTie.Rat hρ' (rdUp r rd)) :
    SeriesTie.Rat hρ rd := by
  refine ⟨fun s x P d => ?_, fun k Q ψ h1 h2 s x P d => ?_, fun Q M h1 s x P d h2 a => ?_⟩
  · have c := g.1 _ _ _ (datum_up h d)
    rewrite [se_theta r ρ i j b] at c
    exact (by exact (c :))
  · have c := g.2.1 k ((by exact (Q :))) ((by exact (ψ :))) ((by exact (h1 :))) ((by exact (h2 :))) _ _ _ (datum_up h d)
    rewrite [se_gens r ρ i j b] at c
    exact (by exact (c :))
  · have c := g.2.2 ((by exact (Q :))) M ((by exact (h1 :))) _ _ _ (datum_up h d) ((by exact (h2 :))) ((by exact (a :)))
    rewrite [se_xi r ρ i j b] at c
    exact (by exact (c :))

end Setup

theorem rat_copy_iff {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (hs : SameSetup ρ ρ') (hρ : ρ.Good) (hρ' : ρ'.Good) (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ')
    (hrd : RdRel h rd rd') (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i') (j : Fin D.R.m) (b : Bool) :
    SeriesTie.Rat hρ (rd i j b) ↔ SeriesTie.Rat hρ' (rd' i' (h.cm j) b) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  obtain rfl := SameData.eq_up r hs
  have e0 : @Eq D.ntw.Tw ((by exact (i :))) ((by exact (i' :))) := (by exact ((@eq_of_heq D.ntw.Tw i ((by exact (i' :))) ((by exact (hi :)))) :))
  have e1 : ∀ (i' : (overD D r).ntw.Tw) (hi : HEq ((by exact (i' :)) : D.ntw.Tw) i') (j' : Fin (overD D r).R.m),
      rd' i' j' b = (by exact ((rdUp r (rd ((by exact (i' :))) ((by exact (j' :))) b)) :)) := fun i' hi j' => by
    refine LinearMap.ext fun f => ?_
    have a := hrd _ i' hi ((by exact (j' :))) b ((by exact (f :)))
    have c : h.fmCast hi ((j' : ℕ) + 1) b ((by exact (f :))) = (by exact (f :)) := (by exact ((eq_of_heq (h.fmCast_heq hi ((j' : ℕ) + 1) b ((by exact (f :))))) :))
    have a' : HEq (rd' i' j' b (h.fmCast hi ((j' : ℕ) + 1) b ((by exact (f :))))) (rd ((by exact (i' :))) ((by exact (j' :))) b ((by exact (f :)))) := (by exact (a :))
    rewrite [c] at a'
    exact (by exact ((@eq_of_heq (GA (overD D r) (Wc (overD D r) j') → ℂ) (rd' i' j' b f) ((by exact ((rd ((i')) ((j')) b ((f))) : _))) ((by exact (a' :)))) :))
  subst e0
  rewrite [e1 _ hi (h.cm j)]
  exact ⟨fun g => (by exact ((rat_up h (hρ' := hρ') g) :)), fun g => rat_dn h (hρ' := hρ') ((by exact (g :)))⟩

end GlobalTheory.TwInputs.Move.RatUp

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatCopyIff =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtremalVectorMemLowestKType =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtremalVectorMemLowestKType", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatCopyIff\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarMulSelfOfPair\nimport Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem cj_phs (X : RealSide D) (j : Fin D.R.m) : cj (twAt D.what₂.embLL X.A3.A.v0) (X.R.phs j) = 1 := by
  rw [X.phs j, map_one]

theorem isNorm_iff (X : RealSide D) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (ν : ℂ) :
    IsNorm X.R X.geo.v₀ B ν ↔ ν ≠ 0 ∧ ∃ c, IsScale X.R X.geo.v₀ B c ∧ ∃ n : ℕ, n ≠ 0 ∧ ν ^ n = c ^ n := by
  unfold IsNorm
  simp only [cj_phs, one_mul]

theorem CopyTw.rank_eq (h : CopyTw D D' ι e) (j : Fin D.R.m) :
    (Vc D j).rank = (Vc D' (h.cm j)).rank ∧ (Wc D j).rank = (Wc D' (h.cm j)).rank := by
  have key : ∀ {R R' : Ranks} {H : Host R} {H' : Host R'} (s : Spaces R H.F H.E) (s' : Spaces R' H'.F H'.E),
      R = R' → HEq H H' → HEq s s' → ∀ k, (s.V k).rank = (s'.V k).rank ∧ (s.W k).rank = (s'.W k).rank := by
    intro R R' H H' s s' h1 h2 h3 k
    subst h1; cases h2; cases h3
    exact ⟨rfl, rfl⟩
  exact key D.sp D'.sp h.gal.R h.gal.host h.sp _

theorem CopyTw.glr_eq (h : CopyTw D D' ι e) (j : Fin D.R.m) : GLR D (Vc D j).rank = GLR D' (Vc D' (h.cm j)).rank := by
  show (D.what₂.Tau → GL (Fin (Vc D j).rank) ℂ) = (D'.what₂.Tau → GL (Fin (Vc D' (h.cm j)).rank) ℂ)
  rw [h.Tau, (h.rank_eq j).1]

theorem CopyTw.pol_eq (h : CopyTw D D' ι e) (j : Fin D.R.m) :
    Formalism.L2.DIV.Pol D'.what₂.LL D.what₂.Tau (Vc D j).rank = Formalism.L2.DIV.Pol D'.what₂.LL D'.what₂.Tau (Vc D' (h.cm j)).rank := by
  rw [h.Tau, (h.rank_eq j).1]

section Coef

variable {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n)

theorem coefFn_add (F G : Formalism.L2.DIV.Pol K D.what₂.Tau n) (x : GLR D n) :
    coefFn σ lam (F + G) x = coefFn σ lam F x + coefFn σ lam G x := by
  simp only [coefFn, map_add (f := _), mul_add]

theorem coefFn_zero (x : GLR D n) : coefFn σ lam (0 : Formalism.L2.DIV.Pol K D.what₂.Tau n) x = 0 := by
  simp only [coefFn, map_zero, mul_zero]

theorem coefFn_smul (a : K) (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) (x : GLR D n) :
    coefFn σ lam (a • F) x = σ a * coefFn σ lam F x := by
  simp only [coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C]
  ring

end Coef

theorem extremalVector_mem_lowestKType (X : RealSide D) {j : Fin D.R.m}
    (hv : FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _)) (τ : D.what₂.Tau) :
    X.geo.v₀ j (sg0 D X.A3.A) τ ∈ lowT (model X j) τ :=
  (hv.1 τ).2.1

theorem harm_move (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (hs : SameSetup ρ ρ') (i : D.ntw.Tw)
    (i' : D'.ntw.Tw) (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (P : PolF D (Wc D j).rank (Vc D j).rank)
    (P' : PolF D' (Wc D' (h.cm j)).rank (Vc D' (h.cm j)).rank) (hP : HEq P P') (x : GLR D (Vc D j).rank)
    (x' : GLR D' (Vc D' (h.cm j)).rank) (hx : HEq x x') :
    harmFn (Wc D' (h.cm j)).rank (ρ'.B i' (h.cm j) b).w (ρ'.B i' (h.cm j) b).F.BS P' x' =
      harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P x := by
  have hB := hs.B i i' hi j (h.cm j) rfl b
  obtain ⟨r, rfl⟩ := h.exists_rest
  have e1 : (ρ'.B i' (h.cm j) b).w.p = (ρ.B i j b).w.p := (eq_of_heq hB.p).symm
  have e2 : (ρ'.B i' (h.cm j) b).w.c = (ρ.B i j b).w.c := (eq_of_heq hB.c).symm
  have e3 : (ρ'.B i' (h.cm j) b).F.BS = (ρ.B i j b).F.BS := (eq_of_heq hB.BS).symm
  have e4 : P' = P := (eq_of_heq hP).symm
  have e5 : x' = x := (eq_of_heq hx).symm
  rw [harmFn_apply, harmFn_apply, e1, e2, e3, e4, e5]
  rfl

theorem coefFn_move (h : CopyTw D D' ι e) (j : Fin D.R.m) (P : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)
    (P' : Formalism.L2.DIV.Pol D'.what₂.LL D'.what₂.Tau (Vc D' (h.cm j)).rank) (hP : HEq (MvPolynomial.map ι P) P')
    (x : GLR D (Vc D j).rank) (x' : GLR D' (Vc D' (h.cm j)).rank) (hx : HEq x x') :
    coefFn D'.what₂.embLL (FWT.lamV D' (h.cm j)) P' x' = coefFn D.what₂.embLL (FWT.lamV D j) P x := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  obtain rfl : P' = MvPolynomial.map ι P := (eq_of_heq hP).symm
  obtain rfl : x' = x := (eq_of_heq hx).symm
  unfold coefFn
  congr 1
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom]
  exact (MvPolynomial.eval₂_map ι _ _ P).trans (by rw [h.embLL_comp]; rfl)

theorem VV_map_mem (h : CopyTw D D' ι e) (j : Fin D.R.m) (P : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)
    (P' : Formalism.L2.DIV.Pol D'.what₂.LL D'.what₂.Tau (Vc D' (h.cm j)).rank) (hP : HEq (MvPolynomial.map ι P) P')
    (hmem : P ∈ VV D.what₂.LL (FWT.lamV D j)) : P' ∈ VV D'.what₂.LL (FWT.lamV D' (h.cm j)) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  obtain rfl : P' = MvPolynomial.map ι P := (eq_of_heq hP).symm
  exact ((baseChangeSpace_holds _ _ ι _ _ (FWT.lamV D j)).1 P).1 hmem

theorem VV_le_span (h : CopyTw D D' ι e) (j : Fin D.R.m) :
    VV D'.what₂.LL (FWT.lamV D' (h.cm j)) ≤ Submodule.span D'.what₂.LL
      {P' | ∃ P ∈ VV D.what₂.LL (FWT.lamV D j), HEq (MvPolynomial.map ι P) P'} := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  refine (le_of_eq (baseChangeSpace_holds _ _ ι _ _ (FWT.lamV D j)).2.symm).trans (Submodule.span_mono ?_)
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨P, hP, HEq.rfl⟩

theorem scale_fwd (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (hs : SameSetup ρ ρ')
    (hv' : ∀ j, FWT.IsChosenExtremalVector X'.R.toRealDat j (sg0 D' X'.A3.A) (X'.geo.v₀ j _)) (i : D.ntw.Tw) (i' : D'.ntw.Tw)
    (hi : HEq i i') (j : Fin D.R.m) (b : Bool) {c : ℂ} (hc : IsScale X.R X.geo.v₀ (ρ.B i j b) c) :
    ∃ c', IsScale X'.R X'.geo.v₀ (ρ'.B i' (h.cm j) b) c' ∧ ∃ n : ℕ, n ≠ 0 ∧ c' ^ n = c ^ n := by
  obtain ⟨g₁, r₁, c₁, hT₁, u, hu, hF⟩ := hc
  obtain ⟨c0, c0', hc0, hc0', hio⟩ := m.io
  obtain ⟨ζ, n, hn, hζ, hζF⟩ := GlobalTheory.CoefUniq.exists_root_of_unity D X c0 c₁ hc0 ⟨g₁, r₁, hT₁⟩ j
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hζ
    exact zero_ne_one hζ
  refine ⟨ζ⁻¹ * c, ?_, n, hn, by rw [mul_pow, inv_pow, hζ, inv_one, one_mul]⟩
  obtain ⟨g', r', hT'⟩ := hc0'
  let u' : ∀ τ, lowT (model X' (h.cm j)) τ := fun τ => ⟨_, extremalVector_mem_lowestKType X' (hv' (h.cm j)) τ⟩
  refine ⟨g', r', c0', hT', u', fun τ => rfl, ?_⟩
  have hsv : SameVec (M := model X j) (M' := model X' (h.cm j)) (fun τ => u τ) (fun τ => u' τ) := by
    intro τ τ' hτ
    have h1 := m.v₀ j (h.cm j) rfl τ τ' hτ
    have h2 := hu τ
    simp only at h2 ⊢
    rw [h2]
    exact h1
  have hG : Submodule.span D'.what₂.LL {P' | ∃ P ∈ VV D.what₂.LL (FWT.lamV D j), HEq (MvPolynomial.map ι P) P'} ≤
      VV D'.what₂.LL (FWT.lamV D' (h.cm j)) := by
    refine Submodule.span_le.2 ?_
    rintro P' ⟨P, hP, hPP'⟩
    exact VV_map_mem h j P P' hPP' hP
  have key : ∀ z ∈ Submodule.span D'.what₂.LL {P' | ∃ P ∈ VV D.what₂.LL (FWT.lamV D j), HEq (MvPolynomial.map ι P) P'},
      ∀ hz : z ∈ VV D'.what₂.LL (FWT.lamV D' (h.cm j)),
      harmFn (Wc D' (h.cm j)).rank (ρ'.B i' (h.cm j) b).w (ρ'.B i' (h.cm j) b).F.BS
          (X'.R.ioP (h.cm j) (PiTensorProduct.tprod ℂ u') (c0' (h.cm j) ⟨z, hz⟩)) =
        (ζ⁻¹ * c) • coefFn D'.what₂.embLL (FWT.lamV D' (h.cm j)) z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨P, hP, hPz⟩ := hz
      intro hz'
      funext x'
      have hx : HEq (cast (h.glr_eq j).symm x') x' := cast_heq _ _
      have e1 := harm_move h hs i i' hi j b (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0 j ⟨P, hP⟩))
        (X'.R.ioP (h.cm j) (PiTensorProduct.tprod ℂ u') (c0' (h.cm j) ⟨z, hz'⟩))
        (hio j (h.cm j) rfl u u' hsv ⟨P, hP⟩ ⟨z, hz'⟩ hPz) _ x' hx
      have e2 := congrFun (hF ⟨P, hP⟩) (cast (h.glr_eq j).symm x')
      rw [show (c₁ j) ⟨P, hP⟩ = ζ • (c0 j) ⟨P, hP⟩ from hζF _, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at e2
      have e3 := coefFn_move h j P z hPz _ x' hx
      have e2' : ζ * harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0 j ⟨P, hP⟩))
          (cast (h.glr_eq j).symm x') = c * coefFn D.what₂.embLL (FWT.lamV D j) P (cast (h.glr_eq j).symm x') := e2
      rw [e1, Pi.smul_apply, smul_eq_mul, e3, mul_assoc, ← e2', ← mul_assoc, inv_mul_cancel₀ hζ0, one_mul]
    | zero =>
      intro hz
      rw [show (⟨0, hz⟩ : ↥(VV D'.what₂.LL (FWT.lamV D' (h.cm j)))) = 0 from rfl, map_zero, map_zero, map_zero]
      funext x'
      rw [Pi.smul_apply, coefFn_zero, smul_zero, Pi.zero_apply]
    | add x y hx hy ihx ihy =>
      intro hxy
      have hx' := hG hx
      have hy' := hG hy
      rw [show (⟨x + y, hxy⟩ : ↥(VV D'.what₂.LL (FWT.lamV D' (h.cm j)))) = ⟨x, hx'⟩ + ⟨y, hy'⟩ from rfl, map_add (f := _), map_add (f := _),
        map_add, ihx hx', ihy hy']
      funext x'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coefFn_add, mul_add]
    | smul a x hx ih =>
      intro hax
      have hx' := hG hx
      rw [show (⟨a • x, hax⟩ : ↥(VV D'.what₂.LL (FWT.lamV D' (h.cm j)))) = a • ⟨x, hx'⟩ from rfl, map_smulₛₗ, map_smul,
        map_smul, ih hx']
      funext x'
      simp only [Pi.smul_apply, smul_eq_mul, coefFn_smul]
      ring
  intro F'
  exact key F' (VV_le_span h j F'.2) F'.2

theorem scale_bwd (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (hs : SameSetup ρ ρ')
    (hv : ∀ j, FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _)) (i : D.ntw.Tw) (i' : D'.ntw.Tw)
    (hi : HEq i i') (j : Fin D.R.m) (b : Bool) {c' : ℂ} (hc : IsScale X'.R X'.geo.v₀ (ρ'.B i' (h.cm j) b) c') :
    ∃ c, IsScale X.R X.geo.v₀ (ρ.B i j b) c ∧ ∃ n : ℕ, n ≠ 0 ∧ c ^ n = c' ^ n := by
  obtain ⟨g₁, r₁, c₁, hT₁, u', hu', hF⟩ := hc
  obtain ⟨c0, c0', hc0, hc0', hio⟩ := m.io
  obtain ⟨ζ, n, hn, hζ, hζF⟩ := GlobalTheory.CoefUniq.exists_root_of_unity D' X' c0' c₁ hc0' ⟨g₁, r₁, hT₁⟩ (h.cm j)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hζ
    exact zero_ne_one hζ
  refine ⟨ζ⁻¹ * c', ?_, n, hn, by rw [mul_pow, inv_pow, hζ, inv_one, one_mul]⟩
  obtain ⟨g, r, hT⟩ := hc0
  obtain ⟨u, hu⟩ : ∃ u : ∀ τ, lowT (model X j) τ, ∀ τ, (u τ : (model X j).sm τ) = X.geo.v₀ j (sg0 D X.A3.A) τ :=
    ⟨fun τ => ⟨_, extremalVector_mem_lowestKType X (hv j) τ⟩, fun τ => rfl⟩
  refine ⟨g, r, c0, hT, u, hu, ?_⟩
  have hsv : SameVec (M := model X j) (M' := model X' (h.cm j)) (fun τ => u τ) (fun τ => u' τ) := by
    intro τ τ' hτ
    have h1 := m.v₀ j (h.cm j) rfl τ τ' hτ
    have h2 := hu' τ'
    have h3 := hu τ
    simp only at h2 h3 ⊢
    rw [h2, h3]
    exact h1
  rintro ⟨P, hP⟩
  funext x
  obtain ⟨P', hPP'⟩ : ∃ P' : Formalism.L2.DIV.Pol D'.what₂.LL D'.what₂.Tau (Vc D' (h.cm j)).rank, HEq (MvPolynomial.map ι P) P' :=
    ⟨cast (h.pol_eq j) (MvPolynomial.map ι P), (cast_heq _ _).symm⟩
  have hP' : P' ∈ VV D'.what₂.LL (FWT.lamV D' (h.cm j)) := VV_map_mem h j P P' hPP' hP
  obtain ⟨x', hx⟩ : ∃ x' : GLR D' (Vc D' (h.cm j)).rank, HEq x x' := ⟨cast (h.glr_eq j) x, (cast_heq _ _).symm⟩
  have e1 := harm_move h hs i i' hi j b (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0 j ⟨P, hP⟩))
    (X'.R.ioP (h.cm j) (PiTensorProduct.tprod ℂ u') (c0' (h.cm j) ⟨P', hP'⟩))
    (hio j (h.cm j) rfl u u' hsv ⟨P, hP⟩ ⟨P', hP'⟩ hPP') x x' hx
  have e2 : ζ * harmFn (Wc D' (h.cm j)).rank (ρ'.B i' (h.cm j) b).w (ρ'.B i' (h.cm j) b).F.BS
      (X'.R.ioP (h.cm j) (PiTensorProduct.tprod ℂ u') (c0' (h.cm j) ⟨P', hP'⟩)) x' =
      c' * coefFn D'.what₂.embLL (FWT.lamV D' (h.cm j)) P' x' := by
    have := congrFun (hF ⟨P', hP'⟩) x'
    rw [show (c₁ (h.cm j)) ⟨P', hP'⟩ = ζ • (c0' (h.cm j)) ⟨P', hP'⟩ from hζF _, map_smul, map_smul] at this
    exact this
  have e3 := coefFn_move h j P P' hPP' x x' hx
  show _ = (ζ⁻¹ * c') * coefFn D.what₂.embLL (FWT.lamV D j) P x
  refine e1.symm.trans ?_
  rw [← e3, mul_assoc, ← e2, ← mul_assoc, inv_mul_cancel₀ hζ0, one_mul]

theorem isNorm_move_iff (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (hs : SameSetup ρ ρ')
    (hv : ∀ j, FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _))
    (hv' : ∀ j, FWT.IsChosenExtremalVector X'.R.toRealDat j (sg0 D' X'.A3.A) (X'.geo.v₀ j _)) (i : D.ntw.Tw) (i' : D'.ntw.Tw)
    (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (ν : ℂ) :
    IsNorm X.R X.geo.v₀ (ρ.B i j b) ν ↔ IsNorm X'.R X'.geo.v₀ (ρ'.B i' (h.cm j) b) ν := by
  rw [isNorm_iff, isNorm_iff]
  constructor
  · rintro ⟨hν, c, hc, n, hn, hνc⟩
    obtain ⟨c', hc', k, hk, hcc⟩ := scale_fwd h m hs hv' i i' hi j b hc
    refine ⟨hν, c', hc', n * k, mul_ne_zero hn hk, ?_⟩
    rw [pow_mul, hνc, ← pow_mul, mul_comm, pow_mul, ← hcc, ← pow_mul, mul_comm, pow_mul]
  · rintro ⟨hν, c', hc', n, hn, hνc⟩
    obtain ⟨c, hc, k, hk, hcc⟩ := scale_bwd h m hs hv i i' hi j b hc'
    refine ⟨hν, c, hc, n * k, mul_ne_zero hn hk, ?_⟩
    rw [pow_mul, hνc, ← pow_mul, mul_comm, pow_mul, ← hcc, ← pow_mul, mul_comm, pow_mul]

theorem scalar_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw} {YS : NX.NExpRealS X.R X.cG S} {S' : NX.RatDat D'.ntw}
    {YS' : NX.NExpRealS X'.R X'.cG S'} {ρ : Setup D.ntw} {ρ' : Setup D'.ntw}, SameSetup ρ ρ' → ∀ (hρ : ρ.Good) (hρ' : ρ'.Good),
    RealPin X.R X.cG ρ → RealPin X'.R X'.cG ρ' →
    (∀ j, FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _)) →
    (∀ j, FWT.IsChosenExtremalVector X'.R.toRealDat j (sg0 D' X'.A3.A) (X'.geo.v₀ j _)) →
    (∀ c : ℂ, RdRel h (fun i j b => realRd YS X.geo.v₀ hρ i j b c) (fun i j b => realRd YS' X'.geo.v₀ hρ' i j b c)) →
    ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b (ν : ℂ),
      IsScalar YS X.geo.v₀ hρ i j b ν → IsScalar YS' X'.geo.v₀ hρ' i' (h.cm j) b ν := by
  intro D D' ι e h X X' m S YS S' YS' ρ ρ' hs hρ hρ' _ _ hv hv' hrd i i' hi j b ν hS
  have hN := fun ν => isNorm_move_iff h m hs hv hv' i i' hi j b ν
  have hR := fun c => RatUp.rat_copy_iff h hs hρ hρ' _ _ (hrd c) i i' hi j b
  exact ⟨hS.ne, fun ⟨ν', h'⟩ => (hN ν).1 (hS.norm ⟨ν', (hN ν').2 h'⟩),
    fun ⟨ν', hn', hr'⟩ => (hR ν).1 (hS.rat ⟨ν', (hN ν').2 hn', (hR ν').2 hr'⟩)⟩

end GlobalTheory.TwInputs.Move
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtremalVectorMemLowestKType =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTieMoveOfPin =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTieMoveOfPin", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwInputs.Move

theorem heckeTie_move_of_pin : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw},
    (∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) (b : Bool),
      HEq (ρ.B i j b).mu (ρ'.B i' (h.cm j) b).mu ∧ HEq (ρ.levK i j b) (ρ'.levK i' (h.cm j) b)) →
    ∀ (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' →
      ∀ (j : Fin D.R.m) b, HeckeTie (rd i j b) → HeckeTie (rd' i' (h.cm j) b) := by
  intro D D' ι e h ρ ρ' hB rd rd' hr i i' hi j b ht
  obtain ⟨hmu, hlev⟩ := hB i i' hi j b
  have hR : ∀ (f : D.nexp.Fm i ((j : ℕ) + 1) b) (f' : D'.nexp.Fm i' ((h.cm j : ℕ) + 1) b), HEq f f' →
      HEq (rd' i' (h.cm j) b f') (rd i j b f) := fun f f' hf => by
    have h1 : h.fmCast hi ((j : ℕ) + 1) b f = f' := eq_of_heq ((h.fmCast_heq hi _ b f).trans hf)
    rw [← h1]
    exact hr i i' hi j b f
  have hj : (j : ℕ) = h.cm j := rfl
  generalize h.cm j = j' at hj hmu hlev hR ⊢
  clear hB hr
  obtain ⟨r, rfl⟩ := h.exists_rest
  cases hi
  obtain rfl : j = j' := Fin.ext hj
  have e0 : ∀ x, rd' i j b x = rd i j b x := fun x => eq_of_heq (hR x x HEq.rfl)
  have hmu' : (ρ'.B i j b).mu = (ρ.B i j b).mu := eq_of_heq hmu.symm
  have hlev' : ρ'.levK i j b = ρ.levK i j b := eq_of_heq hlev.symm
  have hk : ∀ k P R z F, ρ'.hecke i j b k P R z F = ρ.hecke i j b k P R z F := fun k P R z F =>
    funext fun x =>
      (ρ'.hecke_apply i j b k P R z F x).trans
        ((congrArg (fun m : (AE D)ˣ →* Circle =>
            (((m z : Circle) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (k * ((Vc D j).rank / 2)))⁻¹) * ∑ γ ∈ R, F (x * γ)) hmu').trans
          (ρ.hecke_apply i j b k P R z F x).symm)
  have hd : ∀ k P α R z, ρ'.IsHeckeDatum i j b k P α R z ↔ ρ.IsHeckeDatum i j b k P α R z := fun k P α R z =>
    ⟨fun d => ⟨d.1, hlev' ▸ d.2, d.3⟩, fun d => ⟨d.1, hlev'.symm ▸ d.2, d.3⟩⟩
  have ha : ∀ k P f g, HeckeAt (rd' i j b) k P f g ↔ HeckeAt (rd i j b) k P f g := fun k P f g =>
    ⟨fun hg α R z d => (e0 g).symm.trans ((hg α R z ((hd k P α R z).2 d)).trans ((hk k P R z _).trans (congrArg _ (e0 f)))),
      fun hg α R z d => (e0 g).trans ((hg α R z ((hd k P α R z).1 d)).trans ((hk k P R z _).symm.trans (congrArg _ (e0 f).symm)))⟩
  intro k P hkP f hf
  exact (ha k P f _).2 (ht k P hkP f (by obtain ⟨g, hg⟩ := hf; exact ⟨g, (ha k P f g).1 hg⟩))

theorem SameData.mu_levK {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e)
    {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (hs : SameData ρ ρ') (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i')
    (j : Fin D.R.m) (b : Bool) :
    HEq (ρ.B i j b).mu (ρ'.B i' (h.cm j) b).mu ∧ HEq (ρ.levK i j b) (ρ'.levK i' (h.cm j) b) := by
  have hj : (j : ℕ) = h.cm j := rfl
  generalize h.cm j = j' at hj
  obtain ⟨r, rfl⟩ := h.exists_rest
  cases SameData.eq_up r hs
  cases hi
  cases (Fin.ext hj : j = j')
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem heckeTie_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw}, SameData ρ ρ' →
    ∀ (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' →
      ∀ (j : Fin D.R.m) b, HeckeTie (rd i j b) → HeckeTie (rd' i' (h.cm j) b) :=
  fun h _ _ hs => heckeTie_move_of_pin h (hs.mu_levK h)

end GlobalTheory.TwInputs.Move

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTieMoveOfPin =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExtremalVectorOfRealSideBaseChange =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExtremalVectorOfRealSideBaseChange", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

namespace GlobalTheory.TwInputs.Move

theorem isExtremalVector_of_realSideBaseChange : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι), (∀ j, FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _)) →
    ∀ j, FWT.IsChosenExtremalVector X'.R.toRealDat j (sg0 D' X'.A3.A) (X'.geo.v₀ j _) := by
  intro D D' ι e h X X' m _ j
  exact X'.geo.fw.hv₀ j _

end GlobalTheory.TwInputs.Move
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExtremalVectorOfRealSideBaseChange =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingRelationTransferIdentity =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingRelationTransferIdentity", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UnivCharCopy

theorem ring_relation_transfer_identity {R R' : Formalism.BasicNotions.Ranks} {H : Formalism.BasicNotions.Host R} {H' : Formalism.BasicNotions.Host R'} {Ω Ω' : Type}
    [iΩ : Field Ω] [iΩ' : Field Ω'] [aΩ : Algebra H.E Ω] [aΩ' : Algebra H'.E Ω'] {T T' : Type}
    {cc : Ω ≃+* Ω} {cc' : Ω' ≃+* Ω'} {l : T → ℕ} {l' : T' → ℕ}
    {d : ∀ i (Q : Finset (PlE H)) (M : ℕ), G H.E Ω →* Multiplicative (DelQM H (l i) Q M)}
    {d' : ∀ i (Q : Finset (PlE H')) (M : ℕ), G H'.E Ω' →* Multiplicative (DelQM H' (l' i) Q M)}
    (hR : R = R') (hH : HEq H H') (hΩ : Ω = Ω') (hi : HEq iΩ iΩ') (ha : HEq aΩ aΩ') (hcc : HEq cc cc')
    (hT : T = T') (hl : HEq l l') (hd : HEq d d')
    (h : ∀ i Q M, d i Q M = GlobalTheory.GalChar.delU H cc (l i) Q M) :
    ∀ i Q M, d' i Q M = GlobalTheory.GalChar.delU H' cc' (l' i) Q M := by
  subst hR; cases hH; subst hΩ; cases hi; cases ha; cases hcc; subst hT; cases hl; cases hd
  exact h

theorem isUnivChar_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e), GlobalTheory.UnivChar.IsUnivChar D.nexp → GlobalTheory.UnivChar.IsUnivChar D'.nexp := by
  intro D D' ι e h hU
  exact ring_relation_transfer_identity h.gal.R h.gal.host (eq_of_heq h.gal.Om) h.gal.instOm h.gal.algOm h.set.cc
    (eq_of_heq h.set.Tw) h.set.l h.delU hU

end GlobalTheory.UnivCharCopy

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingRelationTransferIdentity =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClassSystem =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClassSystem", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwInputs.Move

variable {D : D7} (r : Rest D)

theorem twistUp_good {A : Type} [CommGroup A] {t : Twist D A} (g : t.Good) : (twistUp r t).Good :=
  ⟨g.1, g.2, g.3, g.4, g.5, g.6⟩

theorem twistDn_good {A : Type} [CommGroup A] {t : Twist (overD D r) A} (g : t.Good) : (twistDn r t).Good :=
  ⟨g.1, g.2, g.3, g.4, g.5, g.6⟩

theorem baseUp_good {S T : HSp D} {B : Base S T} (g : B.Good) : (baseUp r B).Good := by
  have gd := twistUp_good r g.de
  have v := g.frame.vac.2
  refine ⟨g.even, g.odd, ⟨g.frame.1, g.frame.2, g.frame.3, g.frame.4, g.frame.5, g.frame.6, g.frame.7, g.frame.8, g.frame.vac.1, ?_⟩,
    gd, ⟨g.places.1, g.places.2, g.places.3⟩, ⟨g.wt.1, g.wt.2⟩, g.sig, g.sigOK, g.eta, g.hecke, g.real, g.unram, g.tame, g.inf⟩
  exact ⟨v.1, ⟨v.2.1, v.2.2, v.2.3, v.2.4⟩, v.3, v.4, v.5⟩

theorem baseUp_isWeil {S T : HSp D} {B : Base S T} {ν : (AE D)ˣ →* Circle} {ω : PairRep S T}
    (g : B.IsWeil ν ω) : (baseUp r B).IsWeil (D := overD D r) ν ω := by
  refine ⟨g.1, g.2, g.3, g.4, g.5, fun p f a => ?_, fun x y w f a => g.7 x y w f ⟨a.1, a.2, a.3, a.4⟩,
    fun x hx y hy f a => g.8 x hx y hy f ⟨a.1, a.2, a.3, a.4⟩, fun f a => g.9 f ⟨a.1, a.2, a.3, a.4⟩,
    fun μ F h1 h2 p f a => g.10 μ F h1 h2 p f ⟨a.1, a.2, a.3, a.4⟩, fun e he x y h1 h2 z w h3 h4 => ?_⟩
  · have b := g.6 p f ⟨a.1, a.2, a.3, a.4⟩
    exact ⟨b.1, b.2, b.3, b.4⟩
  · obtain ⟨r0, hr, h5⟩ := g.11 e he x y h1 h2 z w h3 h4
    exact ⟨r0, hr, fun l h6 f a => h5 l (fun u hu f a => h6 u hu f ⟨a.1, a.2, a.3, a.4⟩) f ⟨a.1, a.2, a.3, a.4⟩⟩

theorem baseUp_adm {S T : HSp D} {B : Base S T} {Q : Finset (Pl D.host.E)}
    (g : (baseUp r B).admitted Q) : B.admitted Q :=
  ⟨⟨g.1.1, g.1.2, g.1.3⟩, g.2⟩

theorem baseUp_isClassSystem {S T : HSp D} {B : Base S T} {t : Twist (overD D r) Circle} {I : Type}
    {y : I → GA D S} (g : IsClassSystem S (B.levJ (twistDn r t)) y) :
    IsClassSystem (D := overD D r) S ((baseUp r B).levJ t) y :=
  ⟨g.1, g.2, g.3⟩

theorem baseUp_isBaseFrame {S T : HSp D} (B : Base S T) :
    (Lev.IsBaseFrame S B.F.βS B.F.ΛS 1 → Lev.IsBaseFrame (D := overD D r) S (baseUp r B).F.βS (baseUp r B).F.ΛS 1) ∧
    (Lev.IsBaseFrame T B.F.βT B.F.ΛT 1 → Lev.IsBaseFrame (D := overD D r) T (baseUp r B).F.βT (baseUp r B).F.ΛT 1) ∧
    ((∀ P ∈ B.G.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k)) →
      ∀ P ∈ (baseUp r B).G.Pg, ∃ k, P ∈ placesOver (overD D r).host.E ((overD D r).host.g k)) :=
  ⟨id, id, id⟩

theorem cart_onb_over {V : HSp D} {P : D.what₂.Tau → SPar} {P' : (overD D r).what₂.Tau → SPar}
    {M : Mult.DSModel V P} {M' : Mult.DSModel (D := overD D r) V P'} (hm : SameModel M M') :
    HEq (cart M) (cart M') ∧ HEq (onb M) (onb M') := by
  have h1 := hm.ε
  have h2 := hm.fr
  cases M; cases M'
  dsimp only at h1 h2
  subst h1; subst h2
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem chrEq_over {c : (AE D)ˣ →* Circle} {c' : (AE (overD D r))ˣ →* Circle} (hc : HEq c c')
    {χ : Formalism.L2.Host.HChar D.host.E} {χ' : Formalism.L2.Host.HChar (overD D r).host.E} (hχ : HEq χ χ')
    (g : ChrEq (D := D) c χ) : ChrEq (D := overD D r) c' χ' := by
  cases hc; cases hχ
  exact g

end GlobalTheory.TwInputs.Move

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClassSystem =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupRelIffSameData =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupRelIffSameData", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClassSystem\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwInputs.Move

theorem val_move {T T' : Type} {n n' : ℕ} (hT : T = T') (hn : n = n') {a : T → GL (Fin n) ℂ} {a' : T' → GL (Fin n') ℂ}
    {c : T → Matrix (Fin n) (Fin n) ℂ} {c' : T' → Matrix (Fin n') (Fin n') ℂ} (ha : HEq a a') (hc : HEq c c')
    (g : ∀ τ, (a τ).val = c τ) (τ : T') : (a' τ).val = c' τ := by
  subst hT hn ha hc
  exact g τ

theorem grp_move {R R' : Ranks} {H : Host R} {H' : Host R'} {L L' : Fin 2 → Type} (hR : R = R') (hH : HEq H H') (hL : L = L')
    {r r' : ℕ} (e : r = R.r) (e' : r' = R'.r) {A B : Finset (Pl H.E)} {A' B' : Finset (Pl H'.E)} (hA : HEq A A') (hB : HEq B B')
    {u : (∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))) ≃* G0 A r}
    {u' : (∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))) ≃* G0 A' r'} (hu : HEq u u')
    {c : G0 B R.r ≃* ∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))}
    {c' : G0 B' R'.r ≃* ∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))} (hc : HEq c c')
    (g : ∀ x P (h : P ∈ A) (h' : P ∈ B) (a b : Fin r), (u x ⟨P, h⟩).val a b = (c.symm x ⟨P, h'⟩).val (Fin.cast e a) (Fin.cast e b)) :
    ∀ x P (h : P ∈ A') (h' : P ∈ B') (a b : Fin r'),
      (u' x ⟨P, h⟩).val a b = (c'.symm x ⟨P, h'⟩).val (Fin.cast e' a) (Fin.cast e' b) := by
  subst hR; subst hH; subst hL e e' hA hB hu hc
  exact g

theorem setupUp_good {D : D7} (r : Rest D) {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0}
    (h : CopyTw D (overD D r) ι e) {ρ : Setup D.ntw} (g : ρ.Good) : (setupUp r ρ).Good := by
  have grc : (setupUp r ρ).rc.Good := ⟨g.rc.1, g.rc.2, g.rc.3, g.rc.4⟩
  refine ⟨grc, fun i => ⟨(g.ch i).1, (g.ch i).2⟩, g.bad_ne, g.goodSetup_bad_mem_badPlaces,
    g.goodSetup_badPlaces_conj, g.goodSetup_placesOverTwo_subset, g.goodSetup_count_eq_zero_off_badPlaces,
    fun i b x' => ?_, g.ek_e,
    fun i j b => baseUp_good r (g.base i j b),
    fun i j b => (baseUp_isBaseFrame r (ρ.B i j b)).1 (g.latS i j b),
    fun i j b => (baseUp_isBaseFrame r (ρ.B i j b)).2.1 (g.latT i j b),
    fun i j b => (baseUp_isBaseFrame r (ρ.B i j b)).2.2 (g.Pg i j b),
    fun i j b => ?_, fun i j b t ht => ?_, fun i j b t ht ha => ?_⟩
  · have h3 := eq_of_heq (h.sideEmb_heq (i := i) (i' := i) .rfl b x')
    have h4 := h.embLL0_eq x'
    exact (congrArg (ρ.e i b) h3.symm).trans ((g.e_LL0 i b (e x')).trans h4)
  · apply SameTwist.eq
    dsimp only [setupUp, baseUp]
    rw [g.delta i j b]
    exact ⟨.rfl, .rfl, .rfl⟩
  · exact baseUp_isWeil r (g.weil i j b (twistDn r t) (twistDn_good r ht))
  · exact baseUp_isClassSystem r (g.classes i j b (twistDn r t) (twistDn_good r ht) (baseUp_adm r ha))

theorem setupUp_realPin {D : D7} (r : Rest D) {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0}
    (_h : CopyTw D (overD D r) ι e) {X : RealSide D} {X' : RealSide (overD D r)} (m : RealMove X X' ι)
    {ρ : Setup D.ntw} (p : RealPin X.R X.cG ρ) : RealPin X'.R X'.cG (setupUp r ρ) := by
  have chain : ∀ {A A' : Type} {a c : A} {a' c' : A'}, HEq a a' → a = c → HEq c c' → a' = c' :=
    fun h1 h2 h3 => eq_of_heq (h1.symm.trans ((heq_of_eq h2).trans h3))
  constructor
  case deltaPl =>
    intro i t' P' h1 h2
    obtain ⟨t, P, h3, h4⟩ := m.Q i t' P' h1 h2
    cases h4
    exact p.deltaPl i t _ h3 h2
  all_goals
    intro i j b
    have q := sameBase_up r (ρ.B i j b)
    have hMW := cart_onb_over r (m.MW j j rfl)
  · exact chain q.ψ (p.psi i j b) m.ψ
  · exact chain q.θ (p.inf i j b) m.θ
  · exact chain q.sT (p.cartT i j b) hMW.1
  · exact val_move rfl rfl q.BS (m.BV j j rfl) (p.onbS i j b)
  · exact chain q.BT (p.onbT i j b) hMW.2
  · exact chain q.ΛS (p.latS i j b) (m.ΛV j j rfl)
  · exact chain q.ΛT (p.latT i j b) (m.ΛW j j rfl)
  · exact chain q.βS (p.frS i j b) (m.βV j j rfl)
  · exact chain q.βT (p.frT i j b) (m.βW j j rfl)
  · exact chain q.f₀ (p.vac i j b) (m.vacP j j rfl)
  · exact chain q.Pg (p.Pg i j b) m.Pg
  · exact grp_move rfl .rfl rfl (FWT.rank_Wc j) (FWT.rank_Wc (D := overD D r) j) q.Pg m.Pg .rfl m.cG (p.grp i j b)
  · exact chain q.mu0 (p.mu0 i j b) (m.mu0 j)
  · exact chain q.eta (p.eta i j b) m.eta
  · exact chrEq_over r q.de.chi (m.delAt _) (p.delta i j b)
  · exact congrFun (chain q.ap (funext (p.ap i j b)) .rfl)
  · exact congrFun (chain q.am (funext (p.am i j b)) .rfl)

theorem setup_move_data : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyTw D D' ι e → ∀ {X : RealSide D} {X' : RealSide D'}, RealMove X X' ι → ∀ (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ →
    ∃ ρ' : Setup D'.ntw, SameData ρ ρ' ∧ ρ'.Good ∧ RealPin X'.R X'.cG ρ' := by
  intro D D' ι e h X X' m ρ g p
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact ⟨setupUp r ρ, sameData_up r ρ, setupUp_good r h g, setupUp_realPin r h m p⟩

end GlobalTheory.TwInputs.Move

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupRelIffSameData =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupMove =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupMove", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupRelIffSameData\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

namespace GlobalTheory.TwInputs.Move

theorem setup_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ →
    ∃ ρ' : Setup D'.ntw, SameSetup ρ ρ' ∧ ρ'.Good ∧ RealPin X'.R X'.cG ρ' :=
  fun h _ _ m ρ g p => setup_move_data h m ρ g p

end GlobalTheory.TwInputs.Move
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupMove =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSetupOverExtendedDataIntegralFormsEq =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSetupOverExtendedDataIntegralFormsEq", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBasisAtTransport\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwInputs.Move.TieUp

variable {D : D7} (r : Rest D)

theorem placeModel_up {mm nn : ℕ} {ψ B hs e Λ c f₀ T} (h : @IsPlaceModel D mm nn ψ B hs e Λ c f₀ T) :
    @IsPlaceModel (overD D r) mm nn ((ψ)) ((B)) ((hs)) ((e)) ((Λ)) c ((f₀)) ((T)) :=
  @IsPlaceModel.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (trans := h.trans) (modul := h.modul)
    (vac := h.vac)

theorem placeModel_dn {mm nn : ℕ} {ψ B hs e Λ c f₀ T} (h : @IsPlaceModel (overD D r) mm nn ψ B hs e Λ c f₀ T) :
    @IsPlaceModel D mm nn ((ψ)) ((B)) ((hs)) ((e)) ((Λ)) c ((f₀)) ((T)) :=
  @IsPlaceModel.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (trans := h.trans) (modul := h.modul)
    (vac := h.vac)

theorem placeMap_up {S T : HSp D} (B : Base S T) (a : AE D) :
    (baseUp r B).F.placeMap ((a)) = (B.F.placeMap a) := by
  have hP : (fun L : (WO (D := overD D r) S T → ℂ) →ₗ[ℂ] (WO (D := overD D r) S T → ℂ) =>
      IsPlaceModel (baseUp r B).F.ψ (symplO S T)
        (heisO (baseUp r B).F.ψ S T) a (baseUp r B).F.lat 1 (baseUp r B).F.f₀ L) =
      (fun L : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) =>
        IsPlaceModel B.F.ψ (symplO S T) (heisO B.F.ψ S T) a B.F.lat 1 B.F.f₀ L) :=
    funext fun L => propext ⟨fun h => placeModel_dn r h, fun h => placeModel_up r h⟩
  delta Frame.placeMap
  exact congrArg Classical.epsilon hP

theorem vec_up {S T : HSp D} (B : Base S T) (Q ω) :
    (baseUp r B).F.vec (baseUp r B).G Q ω = B.F.vec B.G Q ω := by
  delta Frame.vec
  dsimp only [halfIdem, Frame.datumFn, baseUp]
  exact congrArg (fun f => f (B.F.datumFn B.G Q ω)) (placeMap_up r B (halfIdem B.G.Pg Q))

open Classical in
theorem vecAt_up {S T : HSp D} (B : Base S T) (Q φ) :
    (baseUp r B).vecAt Q φ = B.vecAt Q φ := by
  delta ExportSeries.Base.vecAt
  dsimp only [ExportSeries.Base.locFn, baseUp, twistUp]
  exact vec_up r B (B.de.Q ∪ Q) (B.locFn Q φ)

theorem series_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (Q φ h) :
    series (baseUp r B).F ω ((baseUp r B).vecAt Q φ) h = series B.F ω (B.vecAt Q φ) h := by
  rw [vecAt_up r B, GlobalTheory.TwInputs.Move.RatUp.series_up r B]

theorem theta_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (h : GA D S) :
    (baseUp r B).theta ((ω)) ((h)) = (B.theta ω h) :=
  series_up r B ω ∅ (fun _ _ => 1) h

theorem vecFlat_up {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) :
    (baseUp r B).vecFlat (twistUp r ψ) = (B.vecFlat ψ) :=
  vecAt_up r B ψ.Q _

theorem gen_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) :
    (baseUp r B).gen ((ω)) (twistUp r ψ) = (B.gen ω ψ) := by
  delta ExportSeries.Base.gen
  rw [vecFlat_up r B, GlobalTheory.TwInputs.Move.RatUp.series_up r B]
  rfl

theorem genSet_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) (h P) :
    (baseUp r B).genSet ω (twistUp r ψ) h P = B.genSet ω ψ h P := by
  delta ExportSeries.Base.genSet
  rw [gen_up r B]
  dsimp only [twistUp]
  rfl

def univUp {C : Type} [AddCommGroup C] (u : UnivTwist D C) : UnivTwist (overD D r) C := ⟨u.del, u.kap⟩

theorem vecFam_up {S T : HSp D} (B : Base S T) {C : Type} (Q : Finset (Pl D.host.E))
    (Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) :
    (baseUp r B).vecFam (C := C) Q Φ = B.vecFam (C := C) Q Φ :=
  funext fun _ => vecAt_up r B Q _

theorem xiCoef_up {S T : HSp D} (B : Base S T) {C : Type} [AddCommGroup C] [Fintype C] (ω : PairRep S T) (u : UnivTwist D C)
    (Q : Finset (Pl D.host.E)) (Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) (h : GA D S)
    (P : PolF D T.rank S.rank) :
    (baseUp r B).xiCoef ((ω)) (univUp r u) ((Q)) ((Φ)) ((h)) ((P)) = (B.xiCoef ω u Q Φ h P) := by
  delta ExportSeries.Base.xiCoef ExportSeries.Base.xi
  rw [vecFam_up r B, GlobalTheory.TwInputs.Move.RatUp.series_up r B]
  rfl

theorem classSum_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) {I : Type} [Fintype I] (h : I → GA D S) :
    (baseUp r B).classSum (I := I) ω (twistUp r ψ) h = B.classSum ω ψ h := by
  delta ExportSeries.Base.classSum
  rw [vecFlat_up r B, GlobalTheory.TwInputs.Move.RatUp.series_up r B]
  dsimp only [ExportSeries.Base.levJ, baseUp, twistUp]
  rfl

private theorem baseUp_coefLat {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K]
    (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) :
    (baseUp r B).coefLat σ emb O = B.coefLat σ emb O := by
  funext x
  delta Base.coefLat harmLat
  dsimp only [baseUp]
  rfl

private theorem baseUp_mtLat {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K]
    (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) (t : Twist D Circle) :
    (baseUp r B).mtLat σ emb O (twistUp r t) = B.mtLat σ emb O t := by
  delta Base.mtLat
  rw [baseUp_coefLat r B]
  dsimp only [ExportSeries.Base.levJ, baseUp, twistUp]
  rfl

theorem coefLat_of_equiv {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K] (e : K ≃+* ↥D.LL0) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (hσ : ∀ x, embLL0 D (e x) = σ x) (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ)
    (O : Subring ℂ) : B.coefLat σ emb O = B.coefLat (embLL0 D) (labLL0 D) O := by
  obtain rfl : (embLL0 D).comp e.toRingHom = σ := RingHom.ext hσ
  have h : (fun τ => e.toRingHom.comp (emb τ)) = labLL0 D := funext fun τ => RingHom.ext fun x => (embLL0 D).injective
    ((DFunLike.congr_fun (hemb τ) x).trans (DFunLike.congr_fun (embLL0_labLL0 τ) x).symm)
  funext x
  rw [Base.coefLat, Base.coefLat, harmLat, harmLat, GlobalTheory.CoefLatIso.coefLatFn_ringEquiv, h]

theorem mtLat_of_equiv {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K] (e : K ≃+* ↥D.LL0) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (hσ : ∀ x, embLL0 D (e x) = σ x) (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ)
    (O : Subring ℂ) (t : Twist D Circle) : B.mtLat σ emb O t = B.mtLat (embLL0 D) (labLL0 D) O t := by
  rw [Base.mtLat, Base.mtLat, coefLat_of_equiv B e σ emb hσ hemb]

section Setup

variable (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem liftSetupOverExtendedData_classSum_eq : (setupUp r ρ).sum ((i)) ((j)) b = (ρ.sum i j b) := by
  funext k Q ψ
  delta Setup.sum Setup.tw
  dsimp only [setupUp, twistDn, twistUp]
  exact classSum_up r (ρ.B i j b) (ρ.om i j b (ρ.tw i b k Q ψ).chi) (ρ.tw i b k Q ψ) (ρ.rep i j b (ρ.tw i b k Q ψ))

private theorem univOf_up (Q : Finset (Pl D.host.E)) (M : ℕ) :
    univOf (overD D r).nexp i Q M (setupUp r ρ).rc =
      univUp r (univOf D.nexp i Q M ρ.rc) := by
  dsimp only [setupUp, univOf, univUp, coord, Recip.pull, Recip.sym, resOf, IsResAt]
  rfl

private theorem twistOf_up (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) :
    (setupUp r ρ).tw i b k Q ψ = twistUp r (ρ.tw i b k Q ψ) := by
  dsimp only [Setup.tw, setupUp, twistOf, twistUp, Setup.eOk, Recip.pull, Recip.sym, resOf, IsResAt]
  rfl

variable {r} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (hc : CopyTw D (overD D r) ι e)
include hc

theorem liftSetupOverExtendedData_lat_eq : (setupUp r ρ).lat ((i)) ((j)) b = (ρ.lat i j b) := by
  funext O x
  delta Setup.lat
  dsimp only [setupUp]
  exact (congrFun (baseUp_coefLat r (ρ.B i j b) (embLL0 (overD D r)) (labLL0 (overD D r)) O) (finPt _ x)).trans
    (congrFun (coefLat_of_equiv (ρ.B i j b) e (embLL0 (overD D r)) (labLL0 (overD D r)) hc.embLL0_eq
      (embLL0_labLL0 (D := overD D r)) O) (finPt _ x))

theorem liftSetupOverExtendedData_integralForms_eq : (setupUp r ρ).mt ((i)) ((j)) b = (ρ.mt i j b) := by
  funext k Q ψ
  delta Setup.mt
  dsimp only [setupUp, Setup.eOk]
  exact (congrArg ((baseUp r (ρ.B i j b)).mtLat (embLL0 (overD D r)) (labLL0 (overD D r)) (ρ.eOk i b k).range)
    (twistOf_up r ρ i b k Q ψ)).trans
    ((baseUp_mtLat r (ρ.B i j b) (embLL0 (overD D r)) (labLL0 (overD D r)) (ρ.eOk i b k).range (ρ.tw i b k Q ψ)).trans
      (mtLat_of_equiv (ρ.B i j b) e (embLL0 (overD D r)) (labLL0 (overD D r)) hc.embLL0_eq
        (embLL0_labLL0 (D := overD D r)) (ρ.eOk i b k).range (ρ.tw i b k Q ψ)))

theorem liftSetupOverExtendedData_isDatum_eq : (setupUp r ρ).IsDatum ((i)) ((j)) b = (ρ.IsDatum i j b) := by
  funext s x P
  have hl := liftSetupOverExtendedData_lat_eq ρ i j b hc
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · have m := d.mem
    rw [hl] at m
    exact ⟨d.split, d.off, d.fin, d.supp, m⟩
  · refine ⟨d.split, d.off, d.fin, d.supp, ?_⟩
    rw [hl]
    exact d.mem

end Setup

section Cell

variable {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (hc : CopyTw D (overD D r) ι e)
  {ρ : Setup D.ntw} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool}

def cellUp {hρ : ρ.Good} (hρ' : (setupUp r ρ).Good) {rd : Rd ρ D.nexp i j b} (t : CellTie hρ D.nexp rd) :
    CellTie hρ' (overD D r).nexp (i := i) (j := j) (b := b) rd where
  supp := t.supp
  cls := t.cls
  coef := t.coef
  rdV := t.rdV
  U_eq := t.U_eq
  psiU_eq := t.psiU_eq
  dat := by rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc]; exact t.dat
  dat_onto := by rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc, GlobalTheory.TwInputs.Move.RatUp.se_theta r ρ i j b]; exact t.dat_onto
  lev_iff := t.lev_iff
  th_eq := by rewrite [GlobalTheory.TwInputs.Move.RatUp.se_theta r ρ i j b]; exact t.th_eq
  thPsi_iff := by rewrite [GlobalTheory.TwInputs.Move.RatUp.se_gens r ρ i j b]; exact t.thPsi_iff
  thU_eq := by rewrite [GlobalTheory.TwInputs.Move.RatUp.se_xi r ρ i j b]; exact t.thU_eq
  thU_off := by rewrite [GlobalTheory.TwInputs.Move.RatUp.se_xi r ρ i j b]; exact t.thU_off
  rdV_inj := t.rdV_inj
  mtLat_iff := by rewrite [liftSetupOverExtendedData_integralForms_eq ρ i j b hc]; exact t.mtLat_iff
  thP_eq := by rewrite [liftSetupOverExtendedData_classSum_eq r ρ i j b]; exact t.thP_eq

theorem cellUp_rdV {hρ : ρ.Good} (hρ' : (setupUp r ρ).Good) {rd : Rd ρ D.nexp i j b} (t : CellTie hρ D.nexp rd) :
    HEq t.rdV (cellUp r hc hρ' t).rdV := HEq.rfl

end Cell

end GlobalTheory.TwInputs.Move.TieUp

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSetupOverExtendedDataIntegralFormsEq =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieMove =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieMove", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSetupOverExtendedDataIntegralFormsEq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwInputs.Move.TieUp

theorem rds_eq {D : D7} {r : Rest D} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0}
    (h : CopyTw D (overD D r) ι e) {ρ : Setup D.ntw} {rd : Rds D.nexp ρ} {rd' : Rds (overD D r).nexp (setupUp r ρ)}
    (hr : RdRel h rd rd') : rd' = (rd) := by
  funext i j b
  refine LinearMap.ext fun f => ?_
  have h1 := hr ((i)) i ((HEq.refl i)) ((j)) b ((f))
  refine eq_of_heq ?_
  exact (h1)

theorem tie_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw}, SameSetup ρ ρ' → ∀ (hρ : ρ.Good) (hρ' : ρ'.Good)
    (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ T : Comparison₂ hρ rd,
    ∃ T' : Comparison₂ hρ' rd', ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b,
      HEq (T i j b).rdV (T' i' (h.cm j) b).rdV := by
  intro D D' ι e h ρ ρ' hs hρ hρ' rd rd' hr T
  obtain ⟨r, rfl⟩ := h.exists_rest
  cases SameData.eq_up r hs
  have hrd := rds_eq h hr
  subst hrd
  refine ⟨fun i j b => (cellUp r h hρ' (T i j b)), fun i i' hi j b => ?_⟩
  cases hi
  exact (cellUp_rdV r h hρ' (T i j b))

end GlobalTheory.TwInputs.Move.TieUp

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieMove =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpTiedCopy =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpTiedCopy", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta

noncomputable section

namespace GlobalTheory.HeightCounting.ExpCopy

open GlobalTheory.Mem.R3.Tr

theorem sig_heq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') {T T' : Type} (hT : T = T')
    {f : T ≃ R.Psi} {f' : T' ≃ R'.Psi} (hf : HEq f f') {t : T} {t' : T'} (ht : HEq t t')
    {x : H.E} {x' : H'.E} (hx : HEq x x') :
    HEq (H.sigmaOf ((f t : R.Psi) : R.GG) x)
      (H'.sigmaOf ((f' t' : R'.Psi) : R'.GG) x') := by
  subst hR; cases hH; subst hT; cases hf; cases ht; cases hx; rfl

section
variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem kEmb_heq (h : CopyTw D D' ι e) {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (b : Bool) {t : D.what₂.Tau}
    {t' : D'.what₂.Tau} (ht : HEq t t') {x : D.host.E} {x' : D'.host.E} (hx : HEq x x') :
    HEq (Formalism.L2.NX.kEmb D i b t x) (Formalism.L2.NX.kEmb D' i' b t' x') := by
  have hσ := sig_heq h.gal.R h.gal.host h.Tau h.eTau ht hx
  have hy : e (Formalism.L2.NX.embEL0 D' (D'.host.sigmaOf ((D'.eTau t' : D'.R.Psi) : D'.R.GG) x')) =
      Formalism.L2.NX.embEL0 D (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x) :=
    Subtype.ext (ι.injective ((h.LL0 _).trans (h.map_embE hσ).symm))
  have := h.sideEmb_heq hi b (Formalism.L2.NX.embEL0 D' (D'.host.sigmaOf ((D'.eTau t' : D'.R.Psi) : D'.R.GG) x'))
  rw [hy] at this
  exact this

theorem side_heq (h : CopyTw D D' ι e) {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (b : Bool) (z : ↥D.LL0) :
    HEq (GlobalTheory.SeriesTie.sideEmb D.ntw i b z) (GlobalTheory.SeriesTie.sideEmb D'.ntw i' b (e.symm z)) := by
  have := h.sideEmb_heq hi b (e.symm z)
  rw [e.apply_symm_apply] at this
  exact this

end

theorem infG_eta {D : D7} {cf : CharFrame D} (hcs : CharSide D cf) (t : D.what₂.Tau) :
    D.naut.infG D.naut.etaT (Formalism.L2.Host.embPsi D.host (D.eTau t)) = {(((1 / 2 : ℚ)) : ℂ)} :=
  (hcs.infG D.naut.etaT (fun _ => 1 / 2) (by rw [hcs.etaT]; exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩) (D.eTau t)).1

open Classical in
theorem core (D : D7) (r : Rest D) (X : NExpTied D) (hpl : HEq D.naut.plGw (overD D r).naut.plGw)
    (hhw : ∀ i j b (t : D.what₂.Tau), 1 ≤ j → j ≤ D.R.m →
      ∃ lam : Fin D.R.nV → ℤ, Formalism.L2.NX.HWAtF (Formalism.L2.NX.cE D) (X.rhoW i j b).dual ((by exact NX.kEmb (overD D r) i b t)) lam)
    (hwt : ∀ i j b (t : D.what₂.Tau) (hj : 1 ≤ j) (hjm : j ≤ D.R.m) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
      (overD D r).naut.infG (overD D r).naut.etaT ((by exact embPsi D.host (D.eTau t))) = {sh} →
      Formalism.L2.NX.HWAtF (Formalism.L2.NX.cE D) (X.rhoW i j b).dual ((by exact NX.kEmb (overD D r) i b t)) lam →
      NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh) :
    ∃ X' : NExpTied (overD D r), HEq X.tauG X'.tauG ∧ ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hA : NX.AdmTw D i k Q ψ),
      HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA))).QP ∧
      HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA))).DP ∧
      ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : D.nexp.MtV i j b k Q ψ → Formalism.AUTREP.GAf D.host.E D.R.nV → V),
        GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V ρ →
          GlobalTheory.HeightCounting.Reads X' ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA)) ((by exact ε)) V ((by exact ρ)) := by
  have hpG : ∀ kv, NX.pG (overD D r) kv = NX.pG D kv := fun kv =>
    congrFun (congrFun (eq_of_heq hpl.symm) kv.1) kv.2
  have hxi : ∀ kv, NX.xiRed (overD D r) kv = NX.xiRed D kv := fun kv => by
    unfold NX.xiRed
    have key : ∀ (P₁ P₂ : PlE D.host) (_ : P₁ = P₂)
        (d₁ : Decidable (∃ x : ZMod (D.host.g kv.1), ∃ a c : 𝓞 D.host.E, c ∉ P₁.asIdeal ∧ (a : D.host.E) = D.host.xi0 * c ∧
          ((x.val : 𝓞 D.host.E) * c - a) ∈ P₁.asIdeal))
        (d₂ : Decidable (∃ x : ZMod (D.host.g kv.1), ∃ a c : 𝓞 D.host.E, c ∉ P₂.asIdeal ∧ (a : D.host.E) = D.host.xi0 * c ∧
          ((x.val : 𝓞 D.host.E) * c - a) ∈ P₂.asIdeal)),
        (@dite _ _ d₁ (fun h => h.choose) (fun _ => 0)) = (@dite _ _ d₂ (fun h => h.choose) (fun _ => 0)) := by
      rintro P _ rfl d₁ d₂
      exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)
    exact key _ _ (hpG kv) _ _
  refine ⟨@Formalism.L2.NExpTied.mk (overD D r)
      (U_eq := X.U_eq)
      (psiU_gen := X.psiU_gen)
      (psiU_side := X.psiU_side)
      (psiU_xi := fun i b => (X.psiU_xi i b).imp fun θ ⟨h1, h2⟩ =>
        ⟨h1, fun u => (h2 u).trans (Finset.prod_congr rfl fun kv _ => by rw [hxi kv]; rfl)⟩)
      (delU_cont := X.delU_cont)
      (delU_ine := X.delU_ine)
      (thU_empty := X.thU_empty)
      (sgnT := X.sgnT)
      (sgnT_one := X.sgnT_one)
      (Wt := X.Wt)
      (acgWt := X.acgWt)
      (modWt := X.modWt)
      (fdWt := X.fdWt)
      (rhoW := X.rhoW)
      (rhoW_irr := X.rhoW_irr)
      (rhoW_alg := X.rhoW_alg)
      (tauG := X.tauG)
      (sgnG := X.sgnG)
      (sgnG_one := X.sgnG_one)
      (tau_galois_first_character := fun i j b kv x u h1 h2 h3 h4 => by
        rw [hpG kv] at h3 h4 ⊢
        exact X.tau_galois_first_character i j b kv x u h1 h2 h3 h4)
      (mtV := fun (i : D.ntw.Tw) j b k (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) h1 h2 hA =>
        let m := X.mtV i j b k Q ψ h1 h2 hA
        @Formalism.L2.NX.MtVReal.mk (overD D r) i j b k Q ψ X.sgnT (X.Wt i j b) (X.acgWt i j b) (X.modWt i j b) (X.rhoW i j b) (X.tauG i j b)
          m.W m.acg m.mod m.fd m.ρ m.irr m.alg m.bc m.J m.χ m.J_open m.hyp
          m.QP m.QP_sub m.QP_cover m.QP_nconj m.DP m.DP_sub m.DP_cover m.DP_nconj m.sp
          (fun P hP => m.sp_w P (by
            rcases hP with h | h | ⟨kv, h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨kv, h.trans (hpG kv)⟩)))
          (fun kv => (hpG kv).symm ▸ m.redG kv)
          (fun κ => (m.J_mem κ).trans
            (and_congr Iff.rfl (and_congr (forall_congr' fun kv => by rw [hpG kv]; exact Iff.rfl) Iff.rfl)))
          (fun κ hκ => (m.chi_eq κ hκ).trans
            (congrArg (fun a => a * _ * _)
              (Finset.prod_congr rfl fun kv _ => by
                have key : ∀ {P₁ P₂ : PlE D.host} (hP : P₁ = P₂)
                    (red : (m.sp P₂).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)),
                    NX.gVal D i k b kv (m.sp P₂) red (X.tauG i j b kv) (NX.locM (m.sp P₂) κ) =
                      NX.gVal (overD D r) i k b kv (m.sp P₁) (hP.symm ▸ red) (X.tauG i j b kv) (NX.locM (m.sp P₁) κ) := by
                  rintro P _ rfl _; rfl
                exact key (hpG kv) (m.redG kv))))
          m.real)
      (rhoW_hw := hhw)
      (rhoW_wt := hwt), HEq.refl X.tauG, fun i j b k Q ψ h1 h2 hA => ⟨HEq.rfl, HEq.rfl, fun _ _ _ _ _ hR => hR⟩⟩

theorem expTied_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → CharSide D cf → CharSide D' cf' → ∀ X : NExpTied D, ∃ X' : NExpTied D', (TauTrue X → TauTrue X') ∧ ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)), HEq Q Q' → ∀ (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), HEq ψ ψ' → ∀ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (h2' : j ≤ D'.R.m) (hA' : NX.AdmTw D' i' k Q' ψ'), ∃ hA : NX.AdmTw D i k Q ψ, HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV i' j b k Q' ψ' h1 h2' hA').QP ∧ HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV i' j b k Q' ψ' h1 h2' hA').DP ∧ ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (ε' : FractionRing (D'.ntw.Ok i' k) →+* ℂ), HEq ε ε' → ∀ (V V' : Type) [aV : AddCommGroup V] [mV : Module ℂ V] [aV' : AddCommGroup V'] [mV' : Module ℂ V'], V = V' → HEq aV aV' → HEq mV mV' → ∀ (r : D.nexp.MtV i j b k Q ψ → Formalism.AUTREP.GAf D.host.E D.R.nV → V) (r' : D'.nexp.MtV i' j b k Q' ψ' → Formalism.AUTREP.GAf D'.host.E D'.R.nV → V'), HEq r r' → GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V r → GlobalTheory.HeightCounting.Reads X' i' j b k Q' ψ' h1 h2' hA' ε' V' r' := by
  intro D D' ι e h cf cf' _ hcs hcs' X
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  have hk : ∀ i b t, Formalism.L2.NX.kEmb D i b t = Formalism.L2.NX.kEmb (overD D r) i b t := fun i b t =>
    RingHom.ext fun x => eq_of_heq (kEmb_heq h.cp (i := i) (i' := i) HEq.rfl b (t := t) (t' := t) HEq.rfl (x := x) (x' := x) HEq.rfl)
  obtain ⟨X', hτ, hM⟩ := core D r X h.pl
    (fun i j b t h1 h2 => by
      have := X.rhoW_hw i j b t h1 h2
      rw [hk] at this
      exact this)
    (fun i j b t h1 h2 sh lam hsh hw => by
      refine X.rhoW_wt i j b t h1 h2 sh lam ?_ ?_
      · have h3 : ({(((1 / 2 : ℚ)) : ℂ)} : Multiset ℂ) = {sh} := (infG_eta hcs' t).symm.trans hsh
        exact (infG_eta hcs t).trans h3
      · rw [hk]
        exact hw)
  refine ⟨X', fun ⟨τ, hτ'⟩ => ?_, fun i i' hi j b k Q Q' hQ ψ ψ' hψ h1 h2 h2' hA' => ?_⟩
  · have hτ2 : X'.tauG = X.tauG := eq_of_heq hτ.symm
    refine ⟨fun j kv => (Units.map e.symm.toRingHom.toMonoidHom).comp (τ j kv), fun i j b kv x h1 h2 => ?_⟩
    rw [hτ2]
    exact (hτ' i j b kv x h1 h2).trans
      (eq_of_heq (side_heq h.cp (i := i) (i' := i) HEq.rfl b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)))
  · cases hi; cases hQ; cases hψ
    refine ⟨hA', (hM i j b k Q ψ h1 h2 hA').1, (hM i j b k Q ψ h1 h2 hA').2.1, ?_⟩
    intro ε ε' hε V V' aV mV aV' mV' hV haV hmV ρ ρ' hρ hR
    subst hV; cases haV; cases hmV; cases hε; cases hρ
    exact (hM i j b k Q ψ h1 h2 hA').2.2 ε V ρ hR

end GlobalTheory.HeightCounting.ExpCopy

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpTiedCopy =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsScalarScale =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsScalarScale", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhase\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.HeightCounting
open scoped TensorProduct

namespace GlobalTheory.SerVec

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {v₀ v₁ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem evW_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ}
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₁ j x = (∏ τ, c τ) • evW YS v₀ j x := by
  change (Rl.HW j (sg0 D A3.A)).e _ (v₁ j _) = (∏ τ, c τ) • (Rl.HW j (sg0 D A3.A)).e _ (v₀ j _)
  rw [show v₁ j (sg0 D A3.A) = fun τ => c τ • v₀ j (sg0 D A3.A) τ from funext h]
  exact MultilinearMap.map_smul_univ _ _ _

theorem realRd_scale {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) {j : Fin D.R.m} (b : Bool) {C : ℂ} (hC : C ≠ 0)
    (h : ∀ x, evW YS v₁ j x = C • evW YS v₀ j x) (ν : ℂ) :
    realRd YS v₁ hρ i j b (C * ν) = realRd YS v₀ hρ i j b ν := by
  have key : ∀ x, evK YS v₁ hρ i j b x = C • evK YS v₀ hρ i j b x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
    | tmul a f => rw [evK_tmul, evK_tmul, h, smul_comm]
  refine LinearMap.ext fun f => ?_
  change (C * ν)⁻¹ • evK YS v₁ hρ i j b _ = ν⁻¹ • evK YS v₀ hρ i j b _
  refine (congrArg _ (key _)).trans ?_
  rw [smul_smul, mul_inv, mul_right_comm, inv_mul_cancel₀ hC, one_mul]

theorem isScale_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ}
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) {s : ℂ}
    (hs : IsScale Rl v₀ B s) : IsScale Rl v₁ B ((∏ τ, c τ) * s) := by
  obtain ⟨gramR, c0R, c0L, ht, u, hu, hF⟩ := hs
  refine ⟨gramR, c0R, c0L, ht, fun τ => c τ • u τ, fun τ => ?_, fun F => ?_⟩
  · rw [h, ← hu]; rfl
  · rw [MultilinearMap.map_smul_univ, map_smul, mul_smul, ← hF]
    exact map_smul (GlobalTheory.ExportSeries.harmFn (Wc D j).rank B.w B.F.BS) _ _

theorem isNorm_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ} (hc : ∀ τ, c τ ≠ 0)
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) {ν : ℂ}
    (hν : IsNorm Rl v₀ B ν) : IsNorm Rl v₁ B ((∏ τ, c τ) * ν) := by
  obtain ⟨h0, s, hs, n, hn, he⟩ := hν
  refine ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => hc τ) h0, _, isScale_scale h B hs, n, hn, ?_⟩
  rw [mul_pow, he, ← mul_pow, mul_left_comm]

theorem scale_symm {j : Fin D.R.m} {c : D.what₂.Tau → ℂ} (hc : ∀ τ, c τ ≠ 0)
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (τ : D.what₂.Tau) :
    v₀ j (sg0 D A3.A) τ = (c τ)⁻¹ • v₁ j (sg0 D A3.A) τ := by
  rw [h, smul_smul, inv_mul_cancel₀ (hc τ), one_smul]

theorem isScalar_scale {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) {j : Fin D.R.m} (b : Bool) {c : D.what₂.Tau → ℂ}
    (hc : ∀ τ, c τ ≠ 0) (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) {ν : ℂ}
    (hν : IsScalar YS v₀ hρ i j b ν) : IsScalar YS v₁ hρ i j b ((∏ τ, c τ) * ν) := by
  have hC : (∏ τ, c τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hc τ
  have hc' : ∀ τ, (c τ)⁻¹ ≠ 0 := fun τ => inv_ne_zero (hc τ)
  have h' := scale_symm hc h
  refine ⟨mul_ne_zero hC hν.ne, fun ⟨ν', h1⟩ => isNorm_scale hc h _ (hν.norm ⟨_, isNorm_scale hc' h' _ h1⟩), fun ⟨ν', h1, h2⟩ => ?_⟩
  rw [realRd_scale YS hρ i b hC (evW_scale YS h)]
  refine hν.rat ⟨_, isNorm_scale hc' h' _ h1, ?_⟩
  rw [realRd_scale YS hρ i b (Finset.prod_ne_zero_iff.2 fun τ _ => hc' τ) (evW_scale YS h')]
  exact h2

theorem exists_cell {ρ : Setup D.ntw} {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd rd' : Rd ρ D.nexp i j b}
    (e : rd' = rd) (t : CellTie hρ D.nexp rd) : ∃ t' : CellTie hρ D.nexp rd', t'.rdV = t.rdV := by
  subst e
  exact ⟨t, rfl⟩

theorem serAt_scale {c : Fin D.R.m → D.what₂.Tau → ℂ} (hc : ∀ j τ, c j τ ≠ 0)
    (h : ∀ j τ, v₁ j (sg0 D A3.A) τ = c j τ • v₀ j (sg0 D A3.A) τ)
    (hv : ∀ j, FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₁ j _)) {Xe : Formalism.L2.NExpTied D}
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {cf : Formalism.L2.Host.CharFrame D}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} (Z : SerAt YS v₀ Xe PV cf Pq) :
    Nonempty (SerAt YS v₁ Xe PV cf Pq) := by
  have e : ∀ i j b, realRd YS v₁ Z.ex.good i j b ((∏ τ, c j τ) * Z.ex.ν i j b) = realRd YS v₀ Z.ex.good i j b (Z.ex.ν i j b) :=
    fun i j b => realRd_scale YS _ i b (Finset.prod_ne_zero_iff.2 fun τ _ => hc j τ) (evW_scale YS (h j)) _
  choose t ht using fun i j b => exists_cell (e i j b) (Z.ex.tie i j b)
  refine ⟨{ ex :=
              { ρ := Z.ex.ρ
                good := Z.ex.good
                pin := Z.ex.pin
                vec := hv
                ν := fun i j b => (∏ τ, c j τ) * Z.ex.ν i j b
                scalar := fun i j b => isScalar_scale YS _ i b (hc j) (h j) (Z.ex.scalar i j b)
                tie := t
                hecke := fun i j b => by rw [e]; exact Z.ex.hecke i j b
                univ := Z.ex.univ }
            bad := Z.bad
            ch := Z.ch
            join := fun i j b k Q ψ hA hT => ?_
            sup := Z.sup
            off := Z.off
            lam := Z.lam
            lam_ok := Z.lam_ok
            lam_teich := Z.lam_teich
            lam_C := Z.lam_C
            lam_q := Z.lam_q
            lam_tie := Z.lam_tie }⟩
  obtain ⟨ω, h1, h2⟩ := Z.join i j b k Q ψ hA hT
  refine ⟨ω, h1, fun f g => ?_⟩
  rw [← h2 f g, ← ht i j b]

theorem serAt_vec : ∀ {D : D7} (X : RealSide D) (g₀ g₁ : GlobalTheory.RealGeo.GeoHalf X.core X.R.toRealDat fun _ => 1) {S : NX.RatDat D.ntw} (YS : NX.NExpRealS X.R X.cG S) (Xe : Formalism.L2.NExpTied D) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV) (cf : Formalism.L2.Host.CharFrame D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), SerAt YS g₀.v₀ Xe PV cf Pq → Nonempty (SerAt YS g₁.v₀ Xe PV cf Pq) := by
  intro D X g₀ g₁ S YS Xe PV cf Pq Z
  have hL : ∀ j, FWT.ExtLine (X.R.MW j (sg0 D X.A3.A)) := fun j =>
    GlobalTheory.HolLowOnce.extLine_of_holShape D _ _ _
      (GlobalTheory.DefLift.holShape_fixed D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.char.models.order j).1
  choose c hc h using fun j τ => hL j _ _ (g₀.fw.hv₀ j _).1 (g₁.fw.hv₀ j _).1 τ
  exact serAt_scale YS (fun j τ h0 => by simpa [h0] using hc j τ) h (fun j => g₁.fw.hv₀ j _) Z

end GlobalTheory.SerVec
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsScalarScale =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyAll\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta\npublic import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta

namespace GlobalTheory.HeightCounting.SideCopy.LamCopy

theorem lam_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) → ∃ Z : GlobalTheory.LamTie.LamDat D', Z.Ok ∧ Z.Teich ∧ Z.C = cf' ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D' ∧ GlobalTheory.LamTie.IsLamTieFull D'.ntw Z := by
  rintro D D' ι e h cf cf' ⟨f1, f2, f3, f4⟩ ⟨⟨C, q, w0, c, chi⟩, hOk, hT, rfl, hq, hF⟩
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  have hlam0 : ∀ l j a,
      GlobalTheory.LamTie.LamDat.lam0 (D := overD D r) ⟨cf', q, w0, c, chi⟩ l j a =
      GlobalTheory.LamTie.LamDat.lam0 (D := D) ⟨C, q, w0, c, chi⟩ l j a := by
    cases C; cases cf'
    dsimp only at f1 f2 f3 f4
    subst f1; subst f2; subst f3; subst f4
    intro l j a; rfl
  have he : ∀ x : ↥(overD D r).LL0, (overD D r).what₂.embLL (x : (overD D r).what₂.LL) = D.what₂.embLL (e x : D.what₂.LL) :=
    fun x => (h.cp.embLL0_eq x).symm
  have hjL : (overD D r).ntw.jL = D.ntw.jL := (eq_of_heq h.jL).symm
  have hs2 : (overD D r).ntw.s2 = D.ntw.s2 := (eq_of_heq h.s2).symm
  have hXv : (overD D r).ntw.Xv = D.ntw.Xv := (eq_of_heq h.Xv).symm
  have hLam : ∀ i j lam ja a s,
      GlobalTheory.LamTie.IsLam D.ntw ⟨C, q, w0, c, chi⟩ i j lam ja a s →
      GlobalTheory.LamTie.IsLam (overD D r).ntw ⟨cf', q, w0, c, chi⟩ i j lam ja a s := by
    intro i j lam ja a s ⟨h1, ⟨h2a, h2b, h2c⟩, h3⟩
    exact ⟨hjL ▸ h1, ⟨hs2 ▸ h2a, h2b, h2c⟩, fun P hP => hXv ▸ (hlam0 (D.ntw.l i) ja a).symm ▸ h3 P hP⟩
  refine ⟨⟨cf', q, w0, c, chi⟩, ⟨hOk.places, hOk.aux, hOk.big⟩, hT, rfl, hq, fun i hi => ?_⟩
  obtain ⟨t0, j, t1, t2, t3⟩ := hF i ((h.cp.inW1 i i HEq.rfl).2 hi)
  refine ⟨t0, j, fun x => (congrArg j (he x)).trans ((t1 (e x)).trans
      (congrArg (GlobalTheory.ToricDenom.toBar _ i) (eq_of_heq (h.cp.emb0 i i HEq.rfl x)))),
    fun lam => let ⟨ja, a, s, hl, ht⟩ := t2 lam; ⟨ja, a, s, hLam _ _ _ _ _ _ hl, (hlam0 (D.ntw.l i) ja a).symm ▸ ht⟩,
    fun ja a s b hs hs' => let ⟨lam, hb, hl, ht⟩ := t3 ja a s b hs hs'; ⟨lam, hb, hLam _ _ _ _ _ _ hl, (hlam0 (D.ntw.l i) ja a).symm ▸ ht⟩⟩

end GlobalTheory.HeightCounting.SideCopy.LamCopy
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExportTieMove =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExportTieMove", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepsMatHeqRefl\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtremalVectorMemLowestKType\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTieMoveOfPin\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExtremalVectorOfRealSideBaseChange\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingRelationTransferIdentity\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupMove\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieMove\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpTiedCopy\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsScalarScale\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem exportTie_move (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
    (YS : NX.NExpRealS X.R X.cG S)
    (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b)
    (Z : ExportTie YS X.geo.v₀) :
    ∃ Z' : ExportTie (Forms.tie h m YS hsup) X'.geo.v₀, SameSetup Z.ρ Z'.ρ ∧
      ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b,
        Z'.ν i' (h.cm j) b = Z.ν i j b ∧ HEq (Z.tie i j b).rdV (Z'.tie i' (h.cm j) b).rdV := by
  obtain ⟨ρ', hs, hg, hp⟩ := setup_move h m Z.ρ Z.good Z.pin
  have hrd := Forms.rdRel_move h m YS hsup Z.ρ ρ' hs Z.good hg
  have hm : D'.R.m = D.R.m := (congrArg Ranks.m h.gal.R).symm
  let ν' : D'.ntw.Tw → Fin D'.R.m → Bool → ℂ := fun i' j' b => Z.ν (cast h.Tw_eq.symm i') (Fin.cast hm j') b
  have hν : ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b, ν' i' (h.cm j) b = Z.ν i j b := by
    intro i i' hi j b
    have e1 : cast h.Tw_eq.symm i' = i := eq_of_heq ((cast_heq _ _).trans hi.symm)
    have e2 : Fin.cast hm (h.cm j) = j := Fin.ext rfl
    change Z.ν (cast h.Tw_eq.symm i') (Fin.cast hm (h.cm j)) b = _
    rw [e1, e2]
  have back : ∀ (i' : D'.ntw.Tw) (j' : Fin D'.R.m), ∃ i : D.ntw.Tw, ∃ j : Fin D.R.m, HEq i i' ∧ h.cm j = j' :=
    fun i' j' => ⟨cast h.Tw_eq.symm i', Fin.cast hm j', cast_heq _ _, Fin.ext rfl⟩
  have hrdZ : RdRel h (fun i j b => realRd YS X.geo.v₀ Z.good i j b (Z.ν i j b))
      (fun i j b => realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i j b (ν' i j b)) := by
    intro i i' hi j b f
    have := hrd (Z.ν i j b) i i' hi j b f
    change HEq (realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i' (h.cm j) b (ν' i' (h.cm j) b) _) _
    rw [hν i i' hi j b]
    exact this
  obtain ⟨T', hT'⟩ := TieUp.tie_move h hs Z.good hg _ _ hrdZ Z.tie
  have hv := isExtremalVector_of_realSideBaseChange h m Z.vec
  have hsc : ∀ i' j' b, IsScalar (Forms.tie h m YS hsup) X'.geo.v₀ hg i' j' b (ν' i' j' b) := by
    intro i' j' b
    obtain ⟨i, j, hi, rfl⟩ := back i' j'
    rw [hν i i' hi j b]
    exact scalar_move h m hs Z.good hg Z.pin hp Z.vec hv hrd i i' hi j b _ (Z.scalar i j b)
  have hhk : ∀ i' j' b, HeckeTie (realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i' j' b (ν' i' j' b)) := by
    intro i' j' b
    obtain ⟨i, j, hi, rfl⟩ := back i' j'
    exact heckeTie_move h hs _ _ hrdZ i i' hi j b (Z.hecke i j b)
  exact ⟨ExportTie.mk ρ' hg hp hv ν' hsc T' hhk (GlobalTheory.UnivCharCopy.isUnivChar_copy h Z.univ), hs,
    fun i i' hi j b => ⟨hν i i' hi j b, hT' i i' hi j b⟩⟩

theorem serAt_move (h : CopyAll D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
    (YS : NX.NExpRealS X.R X.cG S) {Xe : NExpTied D} {Xe' : NExpTied D'} (hX : ExpMove Xe Xe')
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {PV' : ∀ i : Fin D'.R.m, principalLevelFrame.RowPsi (Vc D' i) D'.R.nV}
    (hp : KeepsMat fun i => (PV i).ψ) (hp' : KeepsMat fun i => (PV' i).ψ) {cf : CharFrame D} {cf' : CharFrame D'}
    (hcf : SameFrame cf cf') {Pq Pq'} (hPq : HEq Pq Pq') (Z : SerAt YS X.geo.v₀ Xe PV cf Pq) :
    Nonempty (SerAt (Forms.tie h.cp m YS Z.sup) X'.geo.v₀ Xe' PV' cf' Pq') := by
  obtain ⟨Z', hs, hr⟩ := exportTie_move h.cp m YS Z.sup Z.ex
  obtain ⟨lam, l1, l2, l3, l4, l5⟩ := LamCopy.lam_copy h hcf ⟨Z.lam, Z.lam_ok, Z.lam_teich, Z.lam_C, Z.lam_q, Z.lam_tie⟩
  refine ⟨{ ex := Z'
            bad := (low_copy h.cp).2.1 _ _ hs.bad Z.bad
            ch := (pq_copy h.cp Pq Pq' hPq).1 _ _ hs.ch Z.ch
            join := fun i' j' b k Q' ψ' hA' hT' => ?_
            sup := sup_move h.cp m YS Z.sup
            off := (low_copy h.cp).2.2 Z.off
            lam := lam
            lam_ok := l1
            lam_teich := l2
            lam_C := l3
            lam_q := l4
            lam_tie := l5 }⟩
  obtain ⟨j, rfl⟩ : ∃ j, h.cp.cm j = j' := ⟨⟨j', lt_m h.cp j'.2⟩, rfl⟩
  obtain ⟨i, Q, ψ, hi, hQ, hψ, hT, e1, e2, e3, e4⟩ := join_copy h.cp i' j (h.cp.cm j) rfl b k Q' ψ' hT'
  obtain ⟨e5, e6⟩ := e4 _ _ hs.ek
  obtain ⟨hA, -, -, hR⟩ := hX i i' hi ((j : ℕ) + 1) b k Q Q' hQ ψ ψ' hψ (Nat.le_add_left _ _) j.2 (h.cp.cm j).2 hA'
  exact hR _ _ e5 _ _ e1 e2 e3 _ _ (e6 _ _ (hr i i' hi j b).2 _ _ (keepsMat_heq h.cp _ _ hp hp' j (h.cp.cm j) rfl))
    (Z.join i j b k Q ψ hA hT)

theorem series_move (h : CopyAll D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι)
    (g₀ : GlobalTheory.RealGeo.GeoHalf X.core X.R.toRealDat fun _ => 1) (g₁ : GlobalTheory.RealGeo.GeoHalf X'.core X'.R.toRealDat fun _ => 1)
    {kKs hk} (kKs' hk') (YS : NX.NExpRealS X.R X.cG (NX.ratDatR X.R X.cG kKs hk)) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
    (hl : LowIn D) {Sb Sb'} (hSb : OverSet D Sb (lowAll D)) (hSb' : OverSet D' Sb' (lowAll D'))
    {hL hL'} (H : HkAd X Sb hL) (H' : HkAd X' Sb' hL') {hs c} (hs') {c'} (hc : SameUnits c c') (L : HkLaw D _ YS.eF hL hs c)
    {cf : CharFrame D} {cf' : CharFrame D'} (hcf : SameFrame cf cf') (s : CharSide D cf) (s' : CharSide D' cf')
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {PV' : ∀ i : Fin D'.R.m, principalLevelFrame.RowPsi (Vc D' i) D'.R.nV}
    (hp : KeepsMat fun i => (PV i).ψ) (hp' : KeepsMat fun i => (PV' i).ψ) {Pq Pq'} (hPq : HEq Pq Pq')
    {Xe : NExpTied D} (hq : PqLaw Xe Pq) (hτ : TauTrue Xe) (Z : SerAt YS g₀.v₀ Xe PV cf Pq) :
    ∃ (YS' : NX.NExpRealS X'.R X'.cG (NX.ratDatR X'.R X'.cG kKs' hk')) (Xe' : NExpTied D'), PqLaw Xe' Pq' ∧
      HkLaw D' (NX.ratDatR X'.R X'.cG kKs' hk') YS'.eF hL' hs' c' ∧ (∀ i x, HEq ((YS'.fi i).e x) x) ∧
      Nonempty (SerAt YS' g₁.v₀ Xe' PV' cf' Pq') ∧ TauTrue Xe' := by
  obtain rfl : kKs' = m.kKsOf (e := e) YS (NX.idxOf D 0) :=
    RingHom.ext fun x => Subtype.ext ((hk' x).trans (m.kKsOf_spec h.cp YS _ x).symm)
  obtain ⟨Xe', ht, hX⟩ := GlobalTheory.HeightCounting.ExpCopy.expTied_copy h hcf s s' Xe
  obtain ⟨Z₁⟩ := GlobalTheory.SerVec.serAt_vec X g₀ X.geo YS _ _ _ _ Z
  obtain ⟨Z₂⟩ := serAt_move h m YS hX hp hp' hcf hPq Z₁
  exact ⟨Forms.tie h.cp m YS Z₁.sup, Xe', pqLaw_move h.cp hX hPq hq,
    hkLaw_move h.cp m YS hfi hl ((low_copy h.cp).1 hl) hSb hSb' H H' Z₁.sup hs' hc L, fun i x => fiOfEq_heq X' _ x,
    GlobalTheory.SerVec.serAt_vec X' X'.geo g₁ _ _ _ _ _ Z₂, ht hτ⟩

end GlobalTheory.HeightCounting.SerCarry

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExportTieMove =====
