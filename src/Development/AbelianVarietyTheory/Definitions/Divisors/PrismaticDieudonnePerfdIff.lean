module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import ReciprocityTheory.DualLattices.AinfFacts
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Mathlib.RingTheory.Valuation.Integral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd, Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff

-- ===== clump member: Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta\npublic import ReciprocityTheory.DualLattices.AinfFacts\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

structure CycPerfd (p : ℕ) [Fact p.Prime] : Type 1 where
  R : Type
  [ring : CommRing R]
  [nonunit : Fact ¬IsUnit (p : R)]
  [complete : IsAdicComplete (span {(p : R)}) R]
  reg : IsSMulRegular R (p : R)
  ε : PreTilt R p
  zeta_zero : zeta ε 0 = 1
  surj : Function.Surjective (fontaineTheta R p)
  ker_eq : RingHom.ker (fontaineTheta R p) = span {xi ε}

attribute [instance] CycPerfd.ring CycPerfd.nonunit CycPerfd.complete

def CycPerfd.Over {p : ℕ} [Fact p.Prime] (S S' : CycPerfd p) [Algebra S.R S'.R] (α : Ainf p S.R →+* Ainf p S'.R) : Prop :=
  (∀ a, fontaineTheta S'.R p (α a) = algebraMap S.R S'.R (fontaineTheta S.R p a)) ∧
    (∀ a, α (frobenius a) = frobenius (α a)) ∧ α (teichmuller p S.ε) = teichmuller p S'.ε


end GlobalTheory.Published
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\npublic import Mathlib.RingTheory.Valuation.Integral\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.PerfdLat

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

structure PrismData (p : ℕ) [Fact p.Prime] : Type 1 where

  M : ∀ S : CycPerfd p, PDivGroup p S.R → ModuleCat.{0} (Ainf p S.R)

  map : ∀ (S : CycPerfd p) (G H : PDivGroup p S.R), (G ⟶ H) →+ (M S H →ₗ[Ainf p S.R] M S G)

  φ : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G →ₛₗ[(frobenius : Ainf p S.R →+* Ainf p S.R)] M S G

  lie : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G →ₛₗ[fontaineTheta S.R p] G.dual.Lie

  du : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G.dual ≃ₗ[Ainf p S.R] Module.Dual (Ainf p S.R) (M S G)

  l : ∀ S : CycPerfd p, M S (PDivGroup.mu p S.R)

  e : ∀ S : CycPerfd p, M S (const p S.R)

  projective : ∀ S G, Module.Projective (Ainf p S.R) (M S G)

  finite : ∀ S G, Module.Finite (Ainf p S.R) (M S G)

  rank_eq : ∀ S G q, Module.rankAtStalk (R := Ainf p S.R) (M S G) q = G.height

  exists_φ_eq : ∀ S G m, ∃ n, φ S G n = frobenius (xi S.ε) • m

  lie_projective : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), Module.Projective S.R G.dual.Lie

  lie_finite : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), Module.Finite S.R G.dual.Lie

  lie_surjective : ∀ S G, Function.Surjective (lie S G)

  lie_eq_zero_iff : ∀ S G m, lie S G m = 0 ↔ ∃ n, φ S G m = frobenius (xi S.ε) • n

  map_id : ∀ S G, map S G G (𝟙 G) = LinearMap.id

  map_comp : ∀ S G H K (f : G ⟶ H) (g : H ⟶ K), map S G K (f ≫ g) = map S G H f ∘ₗ map S H K g

  map_φ : ∀ S G H (f : G ⟶ H) (m : M S H), map S G H f (φ S H m) = φ S G (map S G H f m)

  lie_map : ∀ S G H (f : G ⟶ H) (m : M S H),
    lie S G (map S G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie S H m)

  du_map : ∀ S G H (f : G ⟶ H) (m : M S H) (x : M S G.dual),
    du S H (map S H.dual G.dual (dualHom G H f) x) m = du S G x (map S G H f m)

  l_bijective : ∀ S, Function.Bijective (LinearMap.toSpanSingleton (Ainf p S.R) _ (l S))

  e_bijective : ∀ S, Function.Bijective (LinearMap.toSpanSingleton (Ainf p S.R) _ (e S))

  φ_l : ∀ S, φ S _ (l S) = frobenius (xi S.ε) • l S

  φ_e : ∀ S, φ S _ (e S) = e S

  map_eps : ∀ S, map S _ _ (epsHom (zeta S.ε) S.zeta_zero (zeta_succ_pow S.ε)) (l S) = Sandwich.mu S.ε • e S

  du_e_l : ∀ S, du S (PDivGroup.mu p S.R) (e S) (l S) = 1

  baseChange : ∀ (S S' : CycPerfd p) [Algebra S.R S'.R] (α : Ainf p S.R →+* Ainf p S'.R), S.Over S' α →
    ∃ bc : ∀ G : PDivGroup p S.R, M S G →ₛₗ[α] M S' (G.baseChange S'.R),
      (∀ G, Submodule.span (Ainf p S'.R) (Set.range (bc G)) = ⊤ ∧ ∀ m, bc G (φ S G m) = φ S' _ (bc G m)) ∧
      (∀ (G H : PDivGroup p S.R) (f : G ⟶ H) (m : M S H),
        bc G (map S G H f m) = map S' _ _ (baseChangeMap S'.R f) (bc H m)) ∧
      ∀ j : PDivGroup.mu p S'.R ⟶ (PDivGroup.mu p S.R).baseChange S'.R,
        (∀ n, j.app n (1 ⊗ₜ AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single 1 1) →
          map S' _ _ j (bc _ (l S)) = l S'

attribute [instance] PrismData.projective PrismData.finite

section Const

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

structure ConstTate (ε : (PDivGroup.mu p O).Tate) (G : PDivGroup p O) : Type where

  t : Fin G.height → G.Tate

  t' : Fin G.height → G.dual.Tate

  pair : ∀ i j, pairing G O (t i) (t' j) = if i = j then ε else 0

theorem pairing_bidual (G : PDivGroup p O) (t : G.Tate) (χ : G.dual.Tate) :
    pairing G.dual O χ (tateCongr O G.bidual t) = pairing G O t χ :=
  muRoot_ext fun n => by
    rw [muRoot_pairing, muRoot_pairing, ← charHom_app_muT]
    change χ.pt n ((dualChar G t).app n _) = _
    rw [dualChar_app_muT, ← apply_charElem]
    rfl

section BaseChange

variable (O' : Type) [CommRing O'] [Algebra O O'] {G : PDivGroup p O}

theorem baseChange_mulP (G : PDivGroup p O) (n : ℕ) : (G.baseChange O').mulP n = PDiv.bcMap O' (G.mulP n) :=
  PDiv.bc_hom_ext fun a => by
    obtain ⟨b, rfl⟩ := G.res_surjective n a
    have h := map_nsmul (AddMonoidHom.mk' (baseChangeMap (G := G) (H := G) O') (baseChangeMap_add O')) p (𝟙 G)
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul ℤ_[p]] at h
    have h1 : baseChangeMap O' ((p : ℤ_[p]) • 𝟙 G) = (p : ℤ_[p]) • 𝟙 (G.baseChange O') :=
      h.trans (congrArg _ ((baseChangeFunctor p O O').map_id G))
    have h2 := congrArg (fun f => Hom.app f (n + 1) (1 ⊗ₜ b)) h1
    simp only [baseChangeMap_app, natCast_smul_id_app] at h2
    rw [PDiv.bcMap_tmul, mulP_res]
    exact ((G.baseChange O').mulP_res n (1 ⊗ₜ b)).trans h2.symm

def bcTate (t : G.Tate) : (G.baseChange O').Tate :=
  ⟨fun n => Algebra.TensorProduct.lift (AlgHom.id O' O') ((Algebra.ofId O O').comp (t.pt n)) fun _ _ => .all _ _,
    fun n => Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => by
      rw [baseChange_mulP]
      simp [t.pt_mulP])⟩

@[simp] theorem bcTate_pt (t : G.Tate) (n : ℕ) (r : O') (a : G.A n) :
    (bcTate O' t).pt n (r ⊗ₜ a) = r * algebraMap O O' (t.pt n a) := rfl


omit [Fact p.Prime] in
theorem isGroupLikeElem_one_tmul (χ : G.dual.Tate) (n : ℕ) :
    IsGroupLikeElem O' ((1 : O') ⊗ₜ[O] charElem χ n) := by
  have h := isGroupLikeElem_charElem χ n
  exact ⟨by simp [h.counit_eq_one], by simp [TensorProduct.comul_tmul, h.comul_eq_tmul_self]⟩

def bcChar (χ : G.dual.Tate) : (G.baseChange O').dual.Tate :=
  ⟨fun n => evalPoint _ (isGroupLikeElem_one_tmul O' χ n), fun n => AlgHom.ext fun φ => by
    change ((G.baseChange O').dual.mulP n φ) ((1 : O') ⊗ₜ[O] charElem χ (n + 1)) = φ.ofConv (1 ⊗ₜ charElem χ n)
    rw [dual_mulP, CartierDual.map_apply, ← res_charElem χ n]
    rfl⟩

@[simp] theorem charElem_bcChar (χ : G.dual.Tate) (n : ℕ) : charElem (bcChar O' χ) n = 1 ⊗ₜ charElem χ n :=
  CartierDual.eq_of_forall_apply (R := O') fun φ => apply_charElem _ n φ

def dualBaseChange (G : PDivGroup p O) : (G.baseChange O').dual ≅ G.dual.baseChange O' where
  hom := ⟨fun n => CartierDual.baseChangeHom O O' (G.A n), fun n => BialgHom.ext fun x => by
    change CartierDual.map ((G.baseChange O').mulP n) _ = _
    rw [baseChange_mulP]
    exact (CartierDual.baseChange_map O' (G.mulP n) x).symm⟩
  inv := ⟨fun n => (CartierDual.baseChange O O' (G.A n)).symm, fun n => BialgHom.ext fun x => by
    obtain ⟨y, rfl⟩ := (CartierDual.baseChange O O' (G.A (n + 1))).surjective x
    change PDiv.bcMap O' (CartierDual.map (G.mulP n)) ((CartierDual.baseChange O O' (G.A (n + 1))).symm
      (CartierDual.baseChange O O' (G.A (n + 1)) y)) = (CartierDual.baseChange O O' (G.A n)).symm
        (CartierDual.map ((G.baseChange O').mulP n) (CartierDual.baseChange O O' (G.A (n + 1)) y))
    rw [baseChange_mulP, PDiv.bcMap, PDiv.bcMap, ← CartierDual.baseChange_map, BialgEquiv.symm_apply_apply,
      BialgEquiv.symm_apply_apply]⟩
  hom_inv_id := PDivGroup.Hom.ext <| funext fun n => BialgHom.ext fun a =>
    (CartierDual.baseChange O O' (G.A n)).apply_symm_apply a
  inv_hom_id := PDivGroup.Hom.ext <| funext fun n => BialgHom.ext fun a =>
    (CartierDual.baseChange O O' (G.A n)).symm_apply_apply a

end BaseChange

namespace ConstTate

variable {ε : (PDivGroup.mu p O).Tate} {G : PDivGroup p O}

variable (c : ConstTate ε G)

def dual : ConstTate ε G.dual where
  t := c.t'
  t' i := tateCongr O G.bidual (c.t i)
  pair j i := by rw [pairing_bidual, c.pair]; simp only [eq_comm]

def al : (Fin G.height → O) →ₗ[O] G.dual.omega := Fintype.linearCombination O fun i => hodgeTate G (c.t i)

def W : Submodule O (Fin G.height → O) := LinearMap.ker c.al

end ConstTate

end Const

section Lattices

open scoped Pointwise

def piMap {A B : Type} [CommRing A] [CommRing B] (σ : A →+* B) (ι : Type) : (ι → A) →ₛₗ[σ] (ι → B) where
  toFun x i := σ (x i)
  map_add' x y := funext fun i => map_add σ (x i) (y i)
  map_smul' a x := funext fun i => map_mul σ a (x i)

variable {p : ℕ} [Fact p.Prime]

section Ring

variable (S : CycPerfd p)

instance thetaSurjective : RingHomSurjective (fontaineTheta S.R p) := ⟨S.surj⟩

def eps : (PDivGroup.mu p S.R).Tate := muTate S.R (zeta S.ε) S.zeta_zero (zeta_succ_pow S.ε)

@[simp] theorem muRoot_eps (n : ℕ) : muRoot (eps S) n = zeta S.ε n := muRoot_muTate ..

end Ring

variable (D : PrismData p) {S : CycPerfd p}

def PrismData.eCoord (S : CycPerfd p) : D.M S (const p S.R) ≃ₗ[Ainf p S.R] Ainf p S.R :=
  (LinearEquiv.ofBijective _ (D.e_bijective S)).symm

@[simp] theorem PrismData.eCoord_smul_e (a : Ainf p S.R) : D.eCoord S (a • D.e S) = a :=
  (LinearEquiv.ofBijective _ (D.e_bijective S)).symm_apply_apply a

abbrev PrismData.Cov (G : PDivGroup p S.R) : Type := D.M S G.dual

variable {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

def coord : D.Cov G →ₗ[Ainf p S.R] (Fin G.height → Ainf p S.R) :=
  LinearMap.pi fun j => (D.eCoord S).toLinearMap ∘ₗ D.map S (const p S.R) G.dual (constHom G.dual (c.t' j))

def K (n : ℕ) : Submodule (Ainf p S.R) (Fin G.height → Ainf p S.R) :=
  Nat.rec (LinearMap.range (coord D c)) (fun _ N => N.comap (piMap frobenius _)) n

def b : D.Cov G →ₛₗ[fontaineTheta S.R p] (Fin G.height → S.R) := (piMap (fontaineTheta S.R p) _).comp (coord D c)


end Lattices

end GlobalTheory.PerfdLat
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff =====
