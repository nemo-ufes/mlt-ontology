import MLTStar.AntiPatterns

/-!
# Stratification: basic, ordered and orderless types

The TPTP fragment stops at second-order types.  This module adds the
stratification apparatus of `mlt_star.als`, which is what makes MLT* a *star*
extension of basic MLT: alongside the ordered types organised into a hierarchy
of orders sits a second kind of type whose instances cut across orders.

* a **basic type** is the top of the specialization hierarchy at some order: the
  type of all individuals, or the Cardelli powertype of a basic type;
* an **ordered type** is a specialization of a basic type — these are exactly
  the types of basic MLT;
* an **orderless type** is any other type — for instance the type of all
  entities, which has instances at every order.

`mlt_star.als` writes the basic types as a biconditional (`b in BasicType iff
… or (some lot : BasicType | powertypeOf[b,lot])`).  In Alloy that is read as a
constraint whose intended solution is the least fixed point; Lean states the
least fixed point directly, as an inductive predicate.
-/

namespace MLTStar

universe u

variable {E : Type u} [Domain E]

/-- The basic types: the type whose instances are exactly the individuals, and
the Cardelli powertype of any basic type. -/
inductive BasicType [Domain E] : E → Prop
  | individuals {b : E} : (∀ e, iof e b ↔ Individual e) → BasicType b
  | powertype {b l : E} : BasicType l → IsPowertypeOf b l → BasicType b

/-- An ordered type is a specialization of a basic type.  These are the
"stratified" types, i.e. the types of basic MLT. -/
def OrderedType (t : E) : Prop := ∃ b, BasicType b ∧ Specializes t b

/-- An orderless type is a type that specializes no basic type. -/
def OrderlessType (t : E) : Prop := IsType t ∧ ¬ OrderedType t

/-- A type that has instances at more than one order, such as the type of all
entities.  Stated as a predicate rather than a constant, so that it can be
discussed without extending `Constants`. -/
def IsUniversal (t : E) : Prop := ∀ e : E, iof e t

/-! ## Elementary facts -/

theorem BasicType.isType [Constants E] {b : E} (h : BasicType b) : IsType b := by
  cases h with
  | individuals hb =>
      obtain ⟨i, hi⟩ := exists_individual (E := E)
      exact ⟨i, (hb i).mpr hi⟩
  | powertype _ hp => exact hp.isType_left

theorem BasicType.orderedType [Constants E] {b : E} (h : BasicType b) : OrderedType b :=
  ⟨b, h, Specializes.refl h.isType⟩

theorem OrderedType.isType {t : E} (h : OrderedType t) : IsType t :=
  h.choose_spec.2.isType_left

/-- Ordered types are closed downwards under specialization. -/
theorem OrderedType.of_specializes {t t' : E} (h : Specializes t t') (h' : OrderedType t') :
    OrderedType t :=
  ⟨h'.choose, h'.choose_spec.1, h.trans h'.choose_spec.2⟩

theorem orderedType_or_orderlessType {t : E} (h : IsType t) :
    OrderedType t ∨ OrderlessType t :=
  (Classical.em (OrderedType t)).imp id fun hn => ⟨h, hn⟩

theorem not_orderedType_and_orderlessType {t : E} :
    ¬ (OrderedType t ∧ OrderlessType t) := fun h => h.2.2 h.1

/-! ## The constants of `a13`–`a15` are basic types

They are, in fact, the first three basic types: `cIndividual` by definition, and
`cFot`, `cSot` because they are Cardelli powertypes of basic types. -/

theorem cIndividual_basicType [Constants E] : BasicType (cIndividual : E) :=
  .individuals iof_cIndividual_iff

theorem cFot_basicType [Constants E] : BasicType (cFot : E) :=
  .powertype cIndividual_basicType cFot_isPowertypeOf_cIndividual

theorem cSot_basicType [Constants E] : BasicType (cSot : E) :=
  .powertype cFot_basicType cSot_isPowertypeOf_cFot

theorem cIndividual_orderedType [Constants E] : OrderedType (cIndividual : E) :=
  cIndividual_basicType.orderedType

theorem cFot_orderedType [Constants E] : OrderedType (cFot : E) :=
  cFot_basicType.orderedType

theorem cSot_orderedType [Constants E] : OrderedType (cSot : E) :=
  cSot_basicType.orderedType

/-! ## The universal type is orderless

This is the result that separates MLT* from basic MLT: the type of all entities
exists, is a type, and cannot be placed at any order. -/

/-- No basic type has every entity as an instance.  A basic type is either the
type of all individuals — and not everything is an individual, since
`cIndividual` is a type — or a Cardelli powertype, whose instances are all
types, whereas at least one individual exists. -/
theorem BasicType.not_universal [Constants E] {b : E} (h : BasicType b) :
    ¬ IsUniversal b := by
  intro huniv
  cases h with
  | individuals hb =>
      exact (hb cIndividual).mp (huniv cIndividual) cIndividual_isType
  | powertype _ hp =>
      obtain ⟨i, hi⟩ := exists_individual (E := E)
      exact hi ((hp.2 i).mp (huniv i)).isType_left

theorem IsUniversal.iof_self {t : E} (h : IsUniversal t) : iof t t := h t

theorem IsUniversal.isType {t : E} (h : IsUniversal t) : IsType t := ⟨t, h t⟩

/-- A universal type specializes nothing but universal types. -/
theorem IsUniversal.specializes {t b : E} (h : IsUniversal t) (hs : Specializes t b) :
    IsUniversal b := fun e => hs.2 e (h e)

/-- The type of all entities is orderless: it is a type, and it specializes no
basic type. -/
theorem IsUniversal.orderlessType [Constants E] {t : E} (h : IsUniversal t) :
    OrderlessType t :=
  ⟨h.isType, fun ⟨_, hb, hs⟩ => hb.not_universal (h.specializes hs)⟩

/-- There is at most one universal type, by extensionality. -/
theorem IsUniversal.unique [Extensional E] {a b : E}
    (h₁ : IsUniversal a) (h₂ : IsUniversal b) : a = b :=
  typeExtensionality h₁.isType h₂.isType fun x => ⟨fun _ => h₂ x, fun _ => h₁ x⟩

/-- A universal type has no order at all — not merely "not the order of any
basic type".  It instantiates itself, so were it first-order it would be one of
its own individuals. -/
theorem IsUniversal.not_firstOrderType {t : E} (h : IsUniversal t) :
    ¬ FirstOrderType t := fun hf => hf.2 t h.iof_self hf.1

theorem IsUniversal.not_secondOrderType {t : E} (h : IsUniversal t) :
    ¬ SecondOrderType t := fun hs => h.not_firstOrderType (hs.2 t h.iof_self)

end MLTStar
