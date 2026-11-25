module

import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetIdNormOneMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMoves
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

noncomputable section

namespace GlobalTheory.Mem.Col2.ChiFacLaw

open GlobalTheory.PeriodTransport GlobalTheory.IdealTransport

theorem detId_image (D : D7) {n : ℕ} (L₀ L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (G G' : Matrix (Fin n) (Fin n) D.host.E) (hu : G * G' = 1)
    (h : ∀ x ∈ L, G.mulVec x ∈ L') (h' : ∀ x ∈ L', G'.mulVec x ∈ L) :
    TaylorLogMetric.detId D L₀ L' = Submodule.span (𝓞 D.host.E) {G.det} * TaylorLogMetric.detId D L₀ L := by
  unfold TaylorLogMetric.detId
  rw [Submodule.span_mul_span, Set.singleton_mul]
  congr 1
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨(G' * A).det, ⟨_, fun v hv => ?_, rfl⟩, ?_⟩
    · rw [← Matrix.mulVec_mulVec]
      exact h' _ (hA v hv)
    · show G.det * (G' * A).det = A.det
      rw [← Matrix.det_mul, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨G * A, fun v hv => ?_, (Matrix.det_mul _ _).symm⟩
    rw [← Matrix.mulVec_mulVec]
    exact h _ (hA v hv)

theorem norm_one_span (D : D7) (z : D.host.E) (hz : z * D.host.conj z = 1) :
    TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {z}) := by
  letI := D.host.cmStar
  have hst : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rw [← hst] at hz
  have key : ∀ w x : D.host.E, x ∈ Submodule.span (𝓞 D.host.E) {w} → star x ∈ Submodule.span (𝓞 D.host.E) {star w} := by
    intro w x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine Submodule.mem_span_singleton.2 ⟨⟨star (r : D.host.E), r.2.map (starRingEnd D.host.E).toIntAlgHom⟩, ?_⟩
    exact (star_mul' (r : D.host.E) w).symm
  refine ⟨Submodule.span (𝓞 D.host.E) {star z}, fun x => ?_, ?_⟩
  · rw [← hst]
    exact ⟨fun h => by simpa using key _ _ h, fun h => by simpa using key _ _ h⟩
  · rw [Submodule.span_mul_span, Set.singleton_mul_singleton, hz, Submodule.one_eq_span]

theorem star_det_mul {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    star ((LinearEquiv.det γ.1 : Eˣ) : E) * ((LinearEquiv.det γ.1 : Eˣ) : E) = 1 := by
  first | exact _root_.GlobalTheory.GO.RetractionModules.star_det_mul | exact @_root_.GlobalTheory.GO.RetractionModules.star_det_mul | apply _root_.GlobalTheory.GO.RetractionModules.star_det_mul <;> assumption

theorem matT_eq {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E') {n : ℕ}
    (x : HomE E n n) : matT e n n x = (e : E →+* E').mapMatrix (LinearMap.toMatrix' x) := rfl

variable {D : D7} {X : Fields} (s : Seam D X)

theorem detId_lat_gmap {n : ℕ} (L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    TaylorLogMetric.detId D L₀ (s.lat (gmap g N)) =
      Submodule.span (𝓞 D.host.E) {s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)} * TaylorLogMetric.detId D L₀ (s.lat N) := by
  have hd : s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) = (matT s.iE n n g.toLinearMap).det := by
    rw [matT_eq, ← RingHom.map_det, LinearMap.det_toMatrix', LinearEquiv.coe_det]
    rfl
  rw [hd]
  refine detId_image D L₀ _ _ _ (matT s.iE n n g.symm.toLinearMap) ?_
    ((matT_carries s.iE N (gmap g N) _).2 fun y hy => ⟨y, hy, rfl⟩) ((matT_carries s.iE (gmap g N) N _).2 ?_)
  · rw [matT_eq, matT_eq, ← map_mul, ← LinearMap.toMatrix'_comp]
    simp
  · rintro _ ⟨y, hy, rfl⟩
    simpa using hy

theorem chi_lat_gmap (hs : s.Ok) {χ : TaylorLogMetric.IdE D → ℂ} (hχ : TaylorLogMetric.IsChi D χ) {n : ℕ} (γ : UF X.E n)
    {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat (gmap γ.1 N))) =
      (∏ τ, X.embC s.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
  letI := D.host.cmStar
  have hst : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h1 : star (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) * s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 := by
    rw [hst, ← hs.2, ← map_mul, star_det_mul, map_one]
  let z : unitary D.host.E := ⟨s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E), h1, by rw [mul_comm]; exact h1⟩
  have hL := sd_lat s hs hN
  rw [detId_lat_gmap, hχ.1 _ _ (norm_one_span D z.1 (by rw [← hst, mul_comm]; exact h1))
    (GlobalTheory.RelDetIdeal.detId_normOne_mul D n _ _ _ (GlobalTheory.ThetaMove.Moved.sd_stdL D n) hL hL).1, hχ.2 z,
    Finset.prod_inv_distrib, ← s.iT.prod_comp]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (hs.1 τ _).symm

theorem chiLaw_ambOf : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → TaylorLogMetric.IsChi D χ → (ambOf s B χ cD).ChiLaw a b := by
  intro D X s cc δ B χ cD a b hs hχ γ γ' N N' hN hN'
  change Base.chiFac χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) =
    (∏ τ, X.embC s.σ₀ τ _) ^ _ * (∏ τ, X.embC s.σ₀ τ _) ^ _ * Base.chiFac χ a b (s.lat N) (s.lat N')
  unfold Base.chiFac
  rw [chi_lat_gmap s hs hχ γ hN, chi_lat_gmap s hs hχ γ' hN', mul_zpow, mul_zpow, inv_zpow', inv_zpow', neg_neg]
  ring

end GlobalTheory.Mem.Col2.ChiFacLaw

end
