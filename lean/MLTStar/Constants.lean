import MLTStar.Powertype

/-!
# The constants of the top fragment of MLT*

Consequences of `a13`–`a15`: the type of individuals, the type of first-order
types and the type of second-order types.

The three constants turn out to form the bottom of the MLT stratification: each
is the Cardelli powertype of the one below it, and their instantiation chain
`cIndividual : cFot : cSot` is forced by the axioms.  Notably, the mere
*existence* of `cIndividual` forces at least one individual to exist
(`exists_individual`), which is why none of these results needs `a4`.
-/

namespace MLTStar

universe u

variable {E : Type u} [Domain E] [Constants E]

theorem iof_cIndividual_iff (x : E) : iof x (cIndividual : E) ↔ Individual x :=
  Constants.cIndividual_spec x

theorem iof_cFot_iff (x : E) : iof x (cFot : E) ↔ FirstOrderType x :=
  Constants.cFot_spec x

theorem iof_cSot_iff (x : E) : iof x (cSot : E) ↔ SecondOrderType x :=
  Constants.cSot_spec x

/-! ## Individuals exist

If nothing were an individual, then nothing would instantiate `cIndividual`, so
`cIndividual` would itself be an individual — a contradiction.  So the theory
cannot be satisfied by a domain of types alone. -/

theorem exists_individual : ∃ x : E, Individual x := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ x : E, ¬ Individual x := fun x hx => hno ⟨x, hx⟩
  exact hall cIndividual fun ⟨y, hy⟩ => hall y ((iof_cIndividual_iff y).mp hy)

/-! ## The chain `cIndividual : cFot : cSot` -/

theorem cIndividual_isType : IsType (cIndividual : E) := by
  obtain ⟨i, hi⟩ := exists_individual (E := E)
  exact ⟨i, (iof_cIndividual_iff i).mpr hi⟩

theorem cIndividual_firstOrderType : FirstOrderType (cIndividual : E) :=
  ⟨cIndividual_isType, fun y hy => (iof_cIndividual_iff y).mp hy⟩

theorem iof_cIndividual_cFot : iof (cIndividual : E) (cFot : E) :=
  (iof_cFot_iff _).mpr cIndividual_firstOrderType

theorem cFot_isType : IsType (cFot : E) := ⟨_, iof_cIndividual_cFot⟩

theorem cFot_secondOrderType : SecondOrderType (cFot : E) :=
  ⟨cFot_isType, fun y hy => (iof_cFot_iff y).mp hy⟩

theorem iof_cFot_cSot : iof (cFot : E) (cSot : E) :=
  (iof_cSot_iff _).mpr cFot_secondOrderType

theorem cSot_isType : IsType (cSot : E) := ⟨_, iof_cFot_cSot⟩

/-! ## Where the chain stops -/

theorem not_firstOrderType_cFot : ¬ FirstOrderType (cFot : E) :=
  fun h => h.2 cIndividual iof_cIndividual_cFot cIndividual_isType

theorem not_secondOrderType_cSot : ¬ SecondOrderType (cSot : E) :=
  fun h => not_firstOrderType_cFot (h.2 cFot iof_cFot_cSot)

/-- `cSot` does not instantiate itself: MLT* stops the constant chain at the
second order rather than closing it into a loop. -/
theorem not_iof_cSot_cSot : ¬ iof (cSot : E) (cSot : E) :=
  fun h => not_secondOrderType_cSot ((iof_cSot_iff _).mp h)

theorem not_firstOrderType_cSot : ¬ FirstOrderType (cSot : E) :=
  fun h => h.2 cFot iof_cFot_cSot cFot_isType

/-! ## The constants are pairwise distinct -/

theorem cIndividual_ne_cFot : (cIndividual : E) ≠ (cFot : E) := fun h =>
  not_firstOrderType_cFot (h ▸ cIndividual_firstOrderType)

theorem cIndividual_ne_cSot : (cIndividual : E) ≠ (cSot : E) := fun h =>
  not_firstOrderType_cSot (h ▸ cIndividual_firstOrderType)

theorem cFot_ne_cSot : (cFot : E) ≠ (cSot : E) := fun h =>
  not_secondOrderType_cSot (h ▸ cFot_secondOrderType)

/-! ## The constants are powertypes

`cFot` is the Cardelli powertype of `cIndividual`, and `cSot` is the Cardelli
powertype of `cFot`.  Both hold definitionally once the specifications of the
constants are unfolded: "type all of whose instances are individuals" and
"specialization of the type of all individuals" are the same condition. -/

theorem cFot_isPowertypeOf_cIndividual : IsPowertypeOf (cFot : E) (cIndividual : E) := by
  refine ⟨cFot_isType, fun t => ?_⟩
  rw [iof_cFot_iff]
  constructor
  · exact fun h => ⟨h.1, fun e he => (iof_cIndividual_iff e).mpr (h.2 e he)⟩
  · exact fun h => ⟨h.1, fun e he => (iof_cIndividual_iff e).mp (h.2 e he)⟩

theorem cSot_isPowertypeOf_cFot : IsPowertypeOf (cSot : E) (cFot : E) := by
  refine ⟨cSot_isType, fun t => ?_⟩
  rw [iof_cSot_iff]
  constructor
  · exact fun h => ⟨h.1, fun e he => (iof_cFot_iff e).mpr (h.2 e he)⟩
  · exact fun h => ⟨h.1, fun e he => (iof_cFot_iff e).mp (h.2 e he)⟩

/-! ## Uniqueness of the constants

TPTP states `a13`–`a15` as biconditionals `∀T, (T = c ↔ …)`, bundling existence
and uniqueness.  Here existence is the data of `Constants` and uniqueness is a
theorem, obtained from `a9`. -/

theorem eq_cIndividual [Extensional E] {t : E} (h : ∀ x : E, iof x t ↔ Individual x) :
    t = (cIndividual : E) := by
  obtain ⟨i, hi⟩ := exists_individual (E := E)
  exact typeExtensionality ⟨i, (h i).mpr hi⟩ cIndividual_isType
    fun x => (h x).trans (iof_cIndividual_iff x).symm

theorem eq_cFot [Extensional E] {t : E} (h : ∀ x : E, iof x t ↔ FirstOrderType x) :
    t = (cFot : E) :=
  typeExtensionality ⟨cIndividual, (h _).mpr cIndividual_firstOrderType⟩ cFot_isType
    fun x => (h x).trans (iof_cFot_iff x).symm

theorem eq_cSot [Extensional E] {t : E} (h : ∀ x : E, iof x t ↔ SecondOrderType x) :
    t = (cSot : E) :=
  typeExtensionality ⟨cFot, (h _).mpr cFot_secondOrderType⟩ cSot_isType
    fun x => (h x).trans (iof_cSot_iff x).symm

end MLTStar
