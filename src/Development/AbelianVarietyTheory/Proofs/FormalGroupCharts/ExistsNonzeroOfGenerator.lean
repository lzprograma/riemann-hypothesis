module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GeneratesOfNonzeroOnSpecialFibre
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointIntegralOpenDisc
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FiniteExtensionRamificationEmbedding

@[expose] public section

noncomputable section

namespace GlobalTheory.IntegralExt

section Lie

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Matrix GlobalTheory.BasisUniv

end Lie

section Int

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open GlobalTheory.ArcQ GlobalTheory.ArcQ.DiscInt GlobalTheory.Frames GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

end Int

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

theorem exists_ext_chart_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (la : HeightOneSpectrum (𝓞 c.F)) (e : ℕ), OverLa la T.V io e → y.IsAlg → ∃ (T' : CDVR) (φ : T.Fr →+* T'.Fr) (y' : IntFr Xo c T' (φ.comp io)) (e' : ℕ), φ.Finite ∧ OverLa la T'.V (φ.comp io) e' ∧ y'.IsAlg ∧ (∀ a : T.V, ∃ b : T'.V, algebraMap T'.V T'.Fr b = φ (algebraMap T.V T.Fr a)) ∧ (letI := io.toAlgebra; letI := (φ.comp io).toAlgebra; FrMap ({ φ with commutes' := fun _ => rfl } : T.Fr →ₐ[c.F] T'.Fr) y.1 y'.1) ∧ (∀ f : Rul Xo c, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f → evI y' f = φ (evI y f) ∧ nval T'.V e' (evI y' f) = nval T.V e (evI y f)) ∧ ∃ C : IntegralChartA3 Xo c T' (φ.comp io) y', FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ ∃ P : PELUnif (maximalIdeal T'.V) C.I.G, P.TorsionIso := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y la e ho hy
  have : Finite (ResidueField T.V) := hy
  obtain ⟨hL, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨G, t, m1, m2, -⟩ := y.2.2
  obtain ⟨W, _, _, _, hc, _, hf, hi, hr, hS⟩ := GlobalTheory.UnifAfterExt.exists_split_baseChange T.V G.G G.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  let T' : Formalism.L2.Pj.CDVR := { V := W }
  obtain ⟨φ, r, hr0, hφ, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' (algebraMap T.V W) hi
    (RingHom.finite_algebraMap.2 hf)
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { φ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := hL.bc _ _ ψ y.1
  let y' : IntFr Xo c T' (φ.comp io) :=
    ⟨z, hL.test _ z, GlobalTheory.IntegralPull.integral_baseChange T T' io (φ.comp io) _ hi ψ hφ y.1 z hz y.2.2⟩
  obtain ⟨C, hC⟩ := (GlobalTheory.IntChartExists.intChart_exists E H Dw l Xo c).2.2 (fun _ => rfl) T' _ y'
  refine ⟨T', φ, y', r * e, ?_, ho.bc φ hr0 hv, hr, fun a => ⟨_, (hφ a).symm⟩, hz, fun f hf => ?_, C, hC,
    GlobalTheory.IntegralPull.exists_unif_of_split T T' _ φ hφ m1 m2 hz.1 C.I.m1 C.I.m2 hS⟩
  · letI := φ.toAlgebra
    exact GlobalTheory.SS.finiteDimensional_of_finite_of_isFractionRing T.V T.Fr W T'.Fr (RingHom.ext fun a => (hφ a).symm)
  · have h : evI y' f = φ (evI y f) := by
      have h1 := y.2.1
      have h2 := y'.2.1
      show evalAt _ _ f z = φ (evalAt _ _ f y.1)
      unfold evalAt
      rw [dite_eq_left h1, dite_eq_left h2]
      exact hL.wd f hf _ _ _ _ _ _ _ z h2.choose_spec.choose_spec.choose_spec
        (Formalism.L2.Pj.frMap_trans (Xo := Xo) (c := c) _ _ _ _ ψ _ y.1 z h1.choose_spec.choose_spec.choose_spec hz)
    exact ⟨h, h ▸ nval_bc φ hr0 hv e _⟩

end GlobalTheory.IntegralExt
