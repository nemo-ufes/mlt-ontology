/-!
# MLT* — signature, definitions and axioms

A Lean 4 encoding of the multi-level theory MLT*, following

* J. P. A. Almeida, C. M. Fonseca, V. A. Carvalho, *A Comprehensive Formal Theory
  for Multi-level Conceptual Modeling*, ER 2017,
  <https://doi.org/10.1007/978-3-319-69904-2_2>

and its machine-readable first-order rendering in `tptp/mlt-star.p` of this
repository.  Labels such as `(a7)` below refer to the TPTP formulae.

## Encoding decisions

* The domain of quantification is an arbitrary type `E`.  TPTP axiom `a1`
  ("every element of the domain is an entity") is discharged by the encoding
  itself and has no counterpart here.

* MLT* has a single primitive, the instantiation relation, carried by the class
  `MLTStar.Domain`.

* Everything the TPTP file states as a *definitional* axiom — `a2`, `a3`,
  `a5`–`a8`, `a10`–`a12`, and the complete/disjoint categorization and
  partitioning definitions — is a Lean `def`.  Definitions are conservative, so
  they cannot introduce inconsistency, and the corresponding TPTP biconditionals
  become `Iff.rfl`.  What is left over as genuine, non-definitional assumptions
  is small:

  - `Extensional.typeExtensionality` (`a9`): coextensive types are identical;
  - `Grounded.grounded` (`a4`): types are ultimately grounded on individuals;
  - `Constants.cIndividual`/`cFot`/`cSot` with their defining properties
    (`a13`–`a15`).

* TPTP `a4` is stated there via an auxiliary first-order theory of sets of types
  (the `singleton`, `unions`, `setidentity`, `membershiptyping` and
  `setsareindividuals` axioms), because first-order logic cannot quantify over
  sets.  Lean can, so that scaffolding disappears: `Grounded.grounded` quantifies
  over *all* classes of types.  This is strictly stronger than the TPTP version,
  which only ranges over the finite non-empty sets that `singleton` and `unions`
  force to exist.  Stronger assumptions prove more, so every theorem verified
  against the TPTP file still holds; `MLTStar.Model` exhibits a model and so
  shows the strengthened theory is nevertheless consistent.

* The theory is classical.  `Classical.em` is used freely, exactly as the
  first-order provers used on `tptp/mlt-star.p` do.

* MLT* deliberately admits self-instantiation — the universal type `Entity` is
  one of its own instances — so `iof` is *not* asserted to be irreflexive or
  acyclic.  `Grounded.grounded` is the weaker well-foundedness condition that MLT*
  actually needs: no non-empty class of types is closed under instantiation.
-/

namespace MLTStar

universe u

/-- The single primitive of MLT*: the instantiation relation over a domain of
entities. -/
class Domain (E : Type u) where
  /-- `iof x t` reads "`x` is an instance of `t`". -/
  iof : E → E → Prop

export Domain (iof)

variable {E : Type u} [Domain E]

/-! ## Entities, individuals and types -/

/-- (a2) An individual is an entity that has no possible instances. -/
def Individual (x : E) : Prop := ¬ ∃ y, iof y x

/-- (a3) A type is an entity that has possible instances.

Named `IsType` rather than `Type` for the obvious reason. -/
def IsType (x : E) : Prop := ∃ y, iof y x

/-- (a5) A first-order type is a type all of whose instances are individuals. -/
def FirstOrderType (x : E) : Prop := IsType x ∧ ∀ y, iof y x → Individual y

/-- (a6) A second-order type is a type all of whose instances are first-order
types. -/
def SecondOrderType (x : E) : Prop := IsType x ∧ ∀ y, iof y x → FirstOrderType y

/-! ## Structural relations between types -/

/-- (a7) `t₁` specializes `t₂` when `t₁` is a type and every instance of `t₁` is
an instance of `t₂`. -/
def Specializes (t₁ t₂ : E) : Prop := IsType t₁ ∧ ∀ e, iof e t₁ → iof e t₂

/-- (a8) Proper specialization: specialization between distinct types. -/
def ProperSpecializes (t₁ t₂ : E) : Prop := Specializes t₁ t₂ ∧ t₁ ≠ t₂

/-- (a10) Cardelli's powertype: the instances of `t₁` are exactly the
specializations of `t₂`. -/
def IsPowertypeOf (t₁ t₂ : E) : Prop :=
  IsType t₁ ∧ ∀ t₃, iof t₃ t₁ ↔ Specializes t₃ t₂

/-- (a11) Odell's powertype, called *categorization* in MLT*: every instance of
`t₁` proper specializes `t₂`. -/
def Categorizes (t₁ t₂ : E) : Prop :=
  IsType t₁ ∧ ∀ t₃, iof t₃ t₁ → ProperSpecializes t₃ t₂

/-- Complete categorization: `t₁` categorizes `t₂` and every instance of `t₂`
instantiates some instance of `t₁`. -/
def CompletelyCategorizes (t₁ t₂ : E) : Prop :=
  Categorizes t₁ t₂ ∧ ∀ e, iof e t₂ → ∃ t₃, iof e t₃ ∧ iof t₃ t₁

/-- Disjoint categorization: `t₁` categorizes `t₂` and distinct instances of `t₁`
have disjoint extensions. -/
def DisjointlyCategorizes (t₁ t₂ : E) : Prop :=
  Categorizes t₁ t₂ ∧ ∀ e t₃ t₄, iof t₃ t₁ → iof t₄ t₁ → iof e t₃ → iof e t₄ → t₃ = t₄

/-- `t₁` partitions `t₂` when it categorizes it both completely and
disjointly. -/
def Partitions (t₁ t₂ : E) : Prop :=
  CompletelyCategorizes t₁ t₂ ∧ DisjointlyCategorizes t₁ t₂

/-- (a12) Subordination, as defined in the ER 2017 paper and in `mlt_star.als`:
every instance of `t₁` proper specializes *some* instance of `t₂`.

`a12_subordinationDef` in `tptp/mlt-star.p` used to quantify universally where
the paper quantifies existentially.  That was an error in the TPTP file rather
than a variant of the theory, and has been corrected there to match this. -/
def IsSubordinateTo (t₁ t₂ : E) : Prop :=
  IsType t₁ ∧ IsType t₂ ∧ ∀ t₃, iof t₃ t₁ → ∃ t₄, iof t₄ t₂ ∧ ProperSpecializes t₃ t₄

/-! ## The axioms -/

/-- TPTP `a9`, the extensionality principle for types.  Only the substantive
direction is stated, since the converse is a consequence of `Eq`.

Kept apart from `Grounded` so that every theorem records in its hypotheses which
of the two non-definitional axioms it actually uses.  It turns out that no
conjecture of `tptp/mlt-star.p` needs `a4`. -/
class Extensional (E : Type u) [Domain E] : Prop where
  /-- (a9) Two types with the same instances are the same type. -/
  typeExtensionality :
    ∀ t₁ t₂ : E, IsType t₁ → IsType t₂ → (∀ x, iof x t₁ ↔ iof x t₂) → t₁ = t₂

/-- TPTP `a4`: types are ultimately grounded on individuals.

Stated as: no non-empty class of types is closed under instantiation.  So
descending along instantiation from any type must leave the class — and,
iterated, must eventually reach an individual (see
`MLTStar.exists_individual_reachable`). -/
class Grounded (E : Type u) [Domain E] : Prop where
  /-- (a4) Types are ultimately grounded on individuals. -/
  grounded :
    ∀ S : E → Prop, (∃ y, S y) → (∀ y, S y → IsType y) →
      ∃ y, S y ∧ ∃ z, iof z y ∧ ¬ S z

/-- (a9) Two types with the same instances are the same type. -/
theorem typeExtensionality [Extensional E] {t₁ t₂ : E}
    (h₁ : IsType t₁) (h₂ : IsType t₂) (h : ∀ x, iof x t₁ ↔ iof x t₂) : t₁ = t₂ :=
  Extensional.typeExtensionality t₁ t₂ h₁ h₂ h

/-- (a4) No non-empty class of types is closed under instantiation. -/
theorem grounded [Grounded E] (S : E → Prop) (hne : ∃ y, S y) (hty : ∀ y, S y → IsType y) :
    ∃ y, S y ∧ ∃ z, iof z y ∧ ¬ S z :=
  Grounded.grounded S hne hty

/-- (a13)–(a15) The three constants of the top fragment of MLT*: the type whose
instances are exactly the individuals, the type whose instances are exactly the
first-order types, and the type whose instances are exactly the second-order
types.

The TPTP file states these as `∀ T, (T = c ↔ …)`, which packs together the
*existence* of the constant and its *uniqueness*.  Here existence is the data of
the class and uniqueness is derived from `typeExtensionality`; see
`MLTStar.eq_cIndividual`, `MLTStar.eq_cFot` and `MLTStar.eq_cSot`. -/
class Constants (E : Type u) [Domain E] where
  /-- The type whose instances are exactly the individuals. -/
  cIndividual : E
  /-- The type whose instances are exactly the first-order types. -/
  cFot : E
  /-- The type whose instances are exactly the second-order types. -/
  cSot : E
  /-- (a13) -/
  cIndividual_spec : ∀ x : E, iof x cIndividual ↔ Individual x
  /-- (a14) -/
  cFot_spec : ∀ x : E, iof x cFot ↔ FirstOrderType x
  /-- (a15) -/
  cSot_spec : ∀ x : E, iof x cSot ↔ SecondOrderType x

export Constants (cIndividual cFot cSot)

end MLTStar
