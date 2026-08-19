import MLTStar.Defs

/-!
# Basic consequences of the MLT* axioms

Includes the TPTP sanity check `typesAndIndividualsPartitionEntity`, the order
properties of specialization, the grounding theorem obtained from `a4`, and the
comparison between the paper's and the TPTP file's notions of subordination.
-/

namespace MLTStar

universe u

variable {E : Type u} [Domain E]

/-! ## Individuals and types -/

/-- Being an individual is exactly failing to be a type. -/
theorem individual_iff_not_isType (x : E) : Individual x ↔ ¬ IsType x := Iff.rfl

theorem not_isType_of_individual {x : E} (h : Individual x) : ¬ IsType x := h

theorem not_individual_of_isType {x : E} (h : IsType x) : ¬ Individual x := fun hi => hi h

/-- Every type has an instance. -/
theorem IsType.exists_instance {t : E} (h : IsType t) : ∃ e, iof e t := h

/-- Anything with an instance is a type. -/
theorem isType_of_iof {e t : E} (h : iof e t) : IsType t := ⟨e, h⟩

/-- TPTP conjecture `typesAndIndividualsPartitionEntity`: types and individuals
are jointly exhaustive and mutually exclusive. -/
theorem typesAndIndividualsPartitionEntity :
    (∀ x : E, IsType x ∨ Individual x) ∧ ¬ ∃ x : E, IsType x ∧ Individual x :=
  ⟨fun x => Classical.em (IsType x), fun ⟨_, ht, hi⟩ => hi ht⟩

/-! ## Order properties of specialization -/

theorem Specializes.isType_left {t₁ t₂ : E} (h : Specializes t₁ t₂) : IsType t₁ := h.1

theorem Specializes.isType_right {t₁ t₂ : E} (h : Specializes t₁ t₂) : IsType t₂ :=
  let ⟨e, he⟩ := h.1
  ⟨e, h.2 e he⟩

theorem Specializes.refl {t : E} (h : IsType t) : Specializes t t := ⟨h, fun _ he => he⟩

theorem Specializes.trans {a b c : E} (h₁ : Specializes a b) (h₂ : Specializes b c) :
    Specializes a c :=
  ⟨h₁.1, fun e he => h₂.2 e (h₁.2 e he)⟩

theorem Specializes.antisymm [Extensional E] {a b : E}
    (h₁ : Specializes a b) (h₂ : Specializes b a) : a = b :=
  typeExtensionality h₁.1 h₂.1 fun x => ⟨fun hx => h₁.2 x hx, fun hx => h₂.2 x hx⟩

theorem ProperSpecializes.specializes {a b : E} (h : ProperSpecializes a b) :
    Specializes a b := h.1

theorem ProperSpecializes.ne {a b : E} (h : ProperSpecializes a b) : a ≠ b := h.2

theorem ProperSpecializes.isType_left {a b : E} (h : ProperSpecializes a b) : IsType a :=
  h.1.isType_left

theorem ProperSpecializes.isType_right {a b : E} (h : ProperSpecializes a b) : IsType b :=
  h.1.isType_right

theorem ProperSpecializes.irrefl {a : E} : ¬ ProperSpecializes a a := fun h => h.2 rfl

/-- Proper specialization is asymmetric: two distinct types cannot proper
specialize each other. -/
theorem ProperSpecializes.asymm [Extensional E] {a b : E}
    (h₁ : ProperSpecializes a b) (h₂ : ProperSpecializes b a) : False :=
  h₁.2 (h₁.1.antisymm h₂.1)

theorem ProperSpecializes.trans [Extensional E] {a b c : E}
    (h₁ : ProperSpecializes a b) (h₂ : ProperSpecializes b c) : ProperSpecializes a c := by
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  intro hac
  subst hac
  exact h₁.2 (h₁.1.antisymm h₂.1)

/-! ## Grounding of types on individuals

TPTP axiom `a4` says that no non-empty class of types is closed under
instantiation.  Iterating it yields the statement that motivates it, and that
`mlt_star.als` records as the fact `typeWellFounded`: descending along
instantiation from a type eventually reaches an individual. -/

/-- `Reaches x z` holds when `z` is `x` itself, or is obtained from `x` by
following instantiation downwards finitely many times: `z` is an instance of an
instance of … of `x`. -/
inductive Reaches [Domain E] (x : E) : E → Prop
  | refl : Reaches x x
  | step {y z : E} : Reaches x y → iof z y → Reaches x z

/-- Every type reaches an individual by descending along instantiation.  This is
the `typeWellFounded` fact of `mlt_star.als`, here *derived* from `a4` rather
than assumed. -/
theorem exists_individual_reachable [Grounded E] {x : E} (hx : IsType x) :
    ∃ i, Reaches x i ∧ Individual i := by
  apply Classical.byContradiction
  intro hcon
  have hty : ∀ i, Reaches x i → IsType i := by
    intro i hr
    exact Classical.byContradiction fun hnt => hcon ⟨i, hr, hnt⟩
  obtain ⟨y, ⟨hry, -⟩, z, hz, hzn⟩ :=
    grounded (fun w => Reaches x w ∧ IsType w) ⟨x, Reaches.refl, hx⟩ (fun _ hy => hy.2)
  exact hzn ⟨Reaches.step hry hz, hty z (Reaches.step hry hz)⟩

/-! ## Subordination

`tptp/mlt-star.p` renders subordination with a universal quantifier where the
ER 2017 paper and `mlt_star.als` use an existential one.  Both readings are
recorded in `MLTStar.Defs`, and the implication below is the only relation
between them that holds in general: the converse fails whenever `t₂` has two
instances that a single instance of `t₁` cannot both proper specialize.  Which
of the two is intended is a question for the theory's authors; see the note in
`lean/README.md`. -/

theorem IsSubordinateTo.isType_left {t₁ t₂ : E} (h : IsSubordinateTo t₁ t₂) :
    IsType t₁ := h.1

theorem IsSubordinateTo.isType_right {t₁ t₂ : E} (h : IsSubordinateTo t₁ t₂) :
    IsType t₂ := h.2.1

/-- The TPTP reading of subordination implies the paper's reading.  The
existential witness is supplied by `IsType t₂`, i.e. by the fact that `t₂`, being
a type, has an instance. -/
theorem isSubordinateTo_of_tptp {t₁ t₂ : E} (h : IsSubordinateTo.tptp t₁ t₂) :
    IsSubordinateTo t₁ t₂ := by
  obtain ⟨h₁, ⟨t₄, ht₄⟩, h₃⟩ := h
  exact ⟨h₁, ⟨t₄, ht₄⟩, fun t₃ ht₃ => ⟨t₄, ht₄, h₃ t₃ t₄ ht₃ ht₄⟩⟩

end MLTStar
