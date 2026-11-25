module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory.SecJet

section Alg

variable (R : Type) [CommRing R]

def sqIdeal (k : ℕ) : Ideal (MvPolynomial (Fin k) R) :=
  Ideal.span (Set.range fun a : Fin k => (MvPolynomial.X a : MvPolynomial (Fin k) R) ^ 2)

abbrev EpsAlg (k : ℕ) : Type := MvPolynomial (Fin k) R ⧸ sqIdeal R k

def eps {k : ℕ} (a : Fin k) : EpsAlg R k := Ideal.Quotient.mk _ (MvPolynomial.X a)

theorem eps_mul_self {k : ℕ} (a : Fin k) : eps R a * eps R a = 0 := by
  rw [eps, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.subset_span ⟨a, rfl⟩

def epsIncl {k : ℕ} (a : Fin k) : DualNumber R →ₐ[R] EpsAlg R k :=
  DualNumber.lift ⟨(Algebra.ofId R (EpsAlg R k), eps R a), eps_mul_self R a,
    fun _ => Commute.all _ _⟩

end Alg

end GlobalTheory.SecJet

namespace GlobalTheory.SecJet

section Geo

variable (R : Type) [CommRing R]

abbrev epsT (k : ℕ) : Over (Sp R) := Over.mk (spMap (algebraMap R (EpsAlg R k)))

theorem spMap_comp_eq {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    spMap (f : A →+* B) ≫ spMap (algebraMap R A) = spMap (algebraMap R B) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact f.comp_algebraMap

def epsIn {k : ℕ} (a : Fin k) : epsT R k ⟶ epsR R :=
  Over.homMk (spMap ((epsIncl R a : DualNumber R →ₐ[R] EpsAlg R k) : DualNumber R →+* EpsAlg R k))
    (spMap_comp_eq R (epsIncl R a))

def epsScaleA (c : R) : DualNumber R →ₐ[R] DualNumber R :=
  { epsScaleR c with commutes' := fun r => by simp [epsScaleR] }

def epsScale (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (spMap_comp_eq R (epsScaleA R c))

variable {R}

def tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) : epsR R ⟶ G :=
  (List.ofFn fun i => epsScale R (c i) ≫ v i).prod

theorem isLieComb_tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) :
    IsLieComb c v (tanComb c v) :=
  ⟨_, fun _ => rfl, rfl⟩

end Geo


end GlobalTheory.SecJet
