module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.CardZerosOnTorsionCosetLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MulAPullbackIsoPowSqSymmetricAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulMemAdjoinOfMemPowRange
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimQuotientLeOne
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.NonemptyGradedAlgebraSubGrading
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

noncomputable section

namespace GlobalTheory.TorsionZero

section Core

open MvPolynomial

variable {K R : Type} [Field K] [CommRing R] [Algebra K R]

theorem card_zeros_le_of_growth [IsAlgClosed K] [IsDomain R] (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
    {m g N B d a : ℕ} (hg : 1 ≤ g) (hN : 1 ≤ N) (x : Fin m → R) (hx : ∀ j, x j ∈ 𝒜 N)
    (hform : ∀ e, ∀ y ∈ 𝒜 (N * e), ∀ i, ∃ (n : ℕ) (G : MvPolynomial (Fin m) K),
      G.IsHomogeneous (n + e) ∧ y * x i ^ n = aeval x G)
    {C : Type} [CommRing C] [IsDomain C] [Algebra K C] (r : Fin m → C) (i₀ : Fin m) (hi₀ : r i₀ = 1)
    (hx₀ : x i₀ ≠ 0)
    (hr : Function.Surjective (aeval r : MvPolynomial (Fin m) K →ₐ[K] C))
    (hrel : ∀ n (G : MvPolynomial (Fin m) K), G.IsHomogeneous n → (aeval x G = 0 ↔ aeval r G = 0))
    (hC : ringKrullDim C = g)
    (hfin : ∀ e, 1 ≤ e → Module.Finite K (𝒜 (N * e)) ∧ Module.finrank K (𝒜 (N * e)) ≤ (B * e) ^ g)
    (s : R) (hs : s ∈ 𝒜 (N * d)) (hs0 : s ≠ 0) {ι : Type} [Finite ι] (f : ι → R)
    (hf : ∀ j, f j ∈ 𝒜 (N * a)) {Pt : Type} (ev : Pt → (R →ₐ[K] K))
    (hcov : ∀ p, ∃ i, ev p (x i) ≠ 0)
    (hpt : ∀ (v : Fin m → K) (i : Fin m), v i = 1 →
      (∀ n (G : MvPolynomial (Fin m) K), G.IsHomogeneous n → aeval x G = 0 → aeval v G = 0) →
      ∃ p, ev p (x i) ≠ 0 ∧ ∀ j, ev p (x j) = v j * ev p (x i))
    (hsep : ∀ p q (c : K), (∀ j, ev p (x j) = c * ev q (x j)) → p = q)
    (Z : Set Pt) (hZ : Z.Finite) (hZf : ∀ p, p ∈ Z ↔ ∀ j, ev p (f j) = 0) :
    Nat.card {p : Pt // p ∈ Z ∧ ev p s = 0} ≤ B ^ g * g.factorial * d * a ^ (g - 1) :=
  card_zeros_le_of_growth_aux 𝒜 (fun T => isIntegral_adjoin_of_mul_pow_mem K T)
    (fun T => graded_bezout_bound K T) hg hN x hx hform r i₀ hi₀ hx₀ hr hrel hC hfin s hs hs0 f hf
    ev hcov hpt hsep Z hZ hZf

end Core

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem card_fibre_zeros_le_of_growth {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Sp K) {L : LB X} (hL : L.IsLB) {R : Type} [CommRing R] [IsDomain R] [Algebra K R]
    {𝒜 : ℕ → Submodule K R} [GradedAlgebra 𝒜] (Φ : ∀ e : ℕ, (lbPow L e).Sec ≃ 𝒜 e)
    (ρ : ∀ j : PUnit → L.ι, R →+* Γ(X, (lbPow L 0).U j))
    (hρc : ∀ j a, ρ j (algebraMap K R a) = constFn p _ a)
    (hρ : ∀ j e (s : (lbPow L e).Sec), ρ j (Φ e s) = s.f j)
    {m g N B d a : ℕ} (hg : 1 ≤ g) (hN : 1 ≤ N) (s : Fin m → (lbPow L N).Sec)
    (U : Fin m → X.Opens) (hU : (fun i => Out.nonzeroLocus (s i)) = U)
    (hcov : ⨆ i, U i = ⊤) (haff : ∀ i, IsAffineOpen (U i))
    (r : ∀ i, Fin m → Γ(X, U i))
    (hr : ∀ i j k, resG X (inf_le_right : U i ⊓ (lbPow L N).U k ≤ _) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hgen : ∀ i (f : Γ(X, U i)), ∃ F : MvPolynomial (Fin m) K,
      f = MvPolynomial.eval₂ (constHom p _) (r i) F)
    (hdim : ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty → ringKrullDim Γ(X, U) = g)
    (hspan : ∀ e, 1 ≤ e → ∃ n ≤ (B * e) ^ g, ∃ b : Fin n → (lbPow L (N * e)).Sec,
      ∀ t : (lbPow L (N * e)).Sec, ∃ c : Fin n → K, ∀ j, t.f j = ∑ i, constFn p _ (c i) * (b i).f j)
    {Pt : Type} (pt : Pt → (Sp K ⟶ X)) (hpt : ∀ z, pt z ≫ p = 𝟙 _) (hinj : Function.Injective pt)
    (hsurj : ∀ z : Sp K ⟶ X, z ≫ p = 𝟙 _ → ∃ w, pt w = z)
    (ν : Pt → Pt) (b : Pt) (hfin : {z | ν z = b}.Finite)
    (hpull : ∀ h : (lbPow L N).Sec, ∃ h' : (lbPow L (N * a)).Sec, ∀ z,
      ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus h' ↔ ⊤ ≤ pt (ν z) ⁻¹ᵁ Out.nonzeroLocus h)
    (u : (lbPow L (N * d)).Sec) (hu : ∃ j, u.f j ≠ 0) :
    Nat.card {z : Pt // ν z = b ∧ ¬ ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus u} ≤
      B ^ g * g.factorial * d * a ^ (g - 1) := by
  subst hU
  exact card_fibre_zeros_le_of_growth_aux p hL Φ ρ hρc hρ
    (fun T => isIntegral_adjoin_of_mul_pow_mem K T) (fun T => graded_bezout_bound K T)
    hg hN s hcov haff r hr hgen hdim hspan pt hpt hinj hsurj ν b hfin hpull u hu

def secOne {X : Scheme.{0}} {M : LB X} (s : M.Sec) : (lbPow M 1).Sec :=
  powSecMk 1 s.f fun i j => by
    rw [pow_one]
    exact s.compat i j

theorem nonzeroLocus_secOne {X : Scheme.{0}} {M : LB X} (s : M.Sec) :
    Out.nonzeroLocus (secOne s) = Out.nonzeroLocus s :=
  nonzeroLocus_powSecMk 1 s.f _

theorem secOne_ratio {X : Scheme.{0}} {M : LB X} (s t : M.Sec) (V : X.Opens) (r : Γ(X, V))
    (h : ∀ k, resG X (inf_le_right : V ⊓ M.U k ≤ M.U k) (s.f k) =
      resG X inf_le_left r * resG X inf_le_right (t.f k)) (k : PUnit → M.ι) :
    resG X (inf_le_right : V ⊓ (lbPow M 1).U k ≤ _) ((secOne s).f k) =
      resG X inf_le_left r * resG X inf_le_right ((secOne t).f k) :=
  fn_ext fun y hy => by
    have hy' : y ∈ V ⊓ M.U (k PUnit.unit) := ⟨hy.1, mem_powChart.1 hy.2⟩
    have e := congrArg (gs (𝟙 X) y _) (h (k PUnit.unit))
    rw [gs_res _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy'] at e
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy]
    exact (gs_res (𝟙 X) y _ hy.2 _).trans (e.trans (congrArg (_ * ·) (gs_res (𝟙 X) y _ hy.2 _).symm))

end GlobalTheory.TorsionZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory


open TorsionZero in
theorem card_zeros_on_torsion_le_of_symmetric_veryAmple :
    Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (σ : Type) [Finite σ] (th : σ → M.Sec) (C d k : ℕ), M.IsLB → SymB M → VAmp P.A.hom M th → (∀ e ≥ 1, ∃ r ≤ (C * e) ^ P.g, SectionsHaveFiniteDimension P.A.hom (lbPow M e) r) → 1 ≤ P.g → (k : K) ≠ 0 → ∀ s : (lbPow M d).Sec, (∃ j, s.f j ≠ 0) → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = 1 ∧ ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus s} ≤ C ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2) := by
  intro hL _ K _ _ P M σ _ th C d k hM hsym hva hgrow hg hk u hu
  have := polAV_isIntegral_of_isAlgClosed K P
  obtain ⟨R, _, _, _, 𝒜, _, Φ, -, -, -, hρ⟩ := SectionRing.exists_sectionRing K P.A.left P.A.hom M hM
  choose ρ hρc hρ using hρ
  obtain ⟨hcov, hs⟩ := hva
  choose haff r hr hgen using hs
  obtain ⟨m, ⟨E⟩⟩ := Finite.exists_equiv_fin σ
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h => hk (by rw [h, Nat.cast_zero])
  have hcard := (hL.mulN (Sp K) P k hk1).2.2.2.2 K (𝟙 _) hk
  have e : ∀ z : Out.baseOver (Sp K) ⟶ P.A, z ^ k = z ≫ Out.mulA P.A k := fun z =>
    (congrArg (· ^ k) (Category.comp_id z).symm).trans (MonObj.comp_pow (𝟙 P.A) k z).symm
  have key := card_fibre_zeros_le_of_growth P.A.hom hM Φ ρ hρc hρ (N := 1) (B := C) (d := d) (a := k ^ 2) hg
    le_rfl (fun i => secOne (th (E.symm i))) (fun i => Out.nonzeroLocus (th (E.symm i)))
    (funext fun i => nonzeroLocus_secOne _)
    ((E.symm.iSup_comp (g := fun i => Out.nonzeroLocus (th i))).trans hcov) (fun i => haff _)
    (fun i j => r (E.symm i) (E.symm j)) (fun i j => secOne_ratio _ _ _ _ (hr _ _)) (fun i f => ?_)
    (SmoothDim.ringKrullDim_affineOpen K P.A.left P.A.hom P.g P.smoothDim)
    (fun n hn => ?_) (Pt := Out.baseOver (Sp K) ⟶ P.A) (fun z => z.left) (fun z => Over.w z)
    (fun z w h => Over.OverMorphism.ext h) (fun z hz => ⟨Over.homMk z hz, rfl⟩) (fun z => z ^ k) 1
    (finite_pow_eq (by rw [hcard]; exact pow_ne_zero _ (by omega)) 1) (fun h => ?_)
    (secCast (Nat.one_mul d).symm u) hu
  · rwa [← pow_mul, show 2 * (P.g - 1) = 2 * P.g - 2 by omega] at key
  · obtain ⟨F, hF⟩ := hgen (E.symm i) f
    refine ⟨MvPolynomial.rename E F, hF.trans ?_⟩
    rw [MvPolynomial.eval₂_rename]
    congr 1
    funext x
    simp
  · rw [Nat.one_mul]
    obtain ⟨l, hl, c, hc⟩ := hgrow n hn
    exact ⟨l, hl, c, fun t => (hc t).exists⟩
  · obtain ⟨h', hh'⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow hM (k ^ 2)) (pull_isLB hM _)
      (LBIso.symm (_root_.GlobalTheory.MulSym.lbIso_mulPull_of_symB K P M k hM hsym)) (secPull (secOfPowOne h) (Out.mulA P.A k).left)
    refine ⟨secCast (Nat.one_mul _).symm h', fun z => ?_⟩
    rw [nonzeroLocus_secCast, hh', nonzeroLocus_secPull, nonzeroLocus_secOfPowOne]
    rw [e z]
    rfl

end GlobalTheory
