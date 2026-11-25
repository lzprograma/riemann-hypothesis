module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasisAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairRecordCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOMulSource
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointsGenerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VPNeZeroCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecFockCore
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem

@[expose] public section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate

noncomputable section

namespace GlobalTheory.AdTh.PhaseMapCore
open GlobalTheory.AdTh.PhaseMap


set_option maxHeartbeats 1600000 in
theorem io_eq_phase_smul_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank), (∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (t : T0) (v : VsV D i O.c'.F), R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' v)) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename lt (MvPolynomial.map (inC O.c') (O.io v))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR
  exact GlobalTheory.AdTh.PhaseMap.io_eq_phase_smul_ofFive D G Pl0 T0 A T R F κ v₀ (GlobalTheory.Core5.of_core hR)

end GlobalTheory.AdTh.PhaseMapCore

end
