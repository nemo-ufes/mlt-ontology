# What the Lean encoding showed

Notes on what came out of encoding MLT* in Lean 4 that was not visible from
`mlt_star.als` or `tptp/mlt-star.p`. Every figure here is produced by
`scripts/AxiomAudit.lean`, which walks proof terms rather than statements, and
every claim is a theorem in `MLTStar/`. `derivation-graph.html` draws the same
data as a graph.

Counts are over the **114** named results in `MLTStar/`, and "reaches an axiom"
means the result's proof term mentions that axiom transitively.

| Rests on | Results |
| --- | --- |
| nothing — the definitions alone | 54 |
| `a13`–`a15` constants | 39 |
| `a9` extensionality | 10 |
| `a4` grounding | 6 |
| `a9` and `a13`–`a15` | 5 |

---

## 1. Most of the axiomatisation is not axioms

`tptp/mlt-star.p` has 23 axioms and 10 conjectures. Sorted by what they turn
into:

| | Count | |
| --- | --- | --- |
| Become Lean `def`s | 12 | `a2`, `a3`, `a5`–`a8`, `a10`–`a12`, and the complete/disjoint categorization and partitioning definitions |
| Become unnecessary | 5 | `singleton`, `unions`, `setidentity`, `membershiptyping`, `setsareindividuals` |
| Discharged by the encoding | 1 | `a1` — the domain of quantification *is* a type |
| Survive as assumptions | 5 | `a4`, `a9`, `a13`, `a14`, `a15` |

The twelve definitional axioms are biconditionals introducing a new predicate
from existing ones. As Lean `def`s they are conservative extensions: they
cannot introduce inconsistency, and the corresponding TPTP biconditionals hold
by `Iff.rfl`. First-order logic cannot mark that distinction — an axiom is an
axiom — so the file reads as a far larger commitment than it is.

What you actually have to trust is three things, kept in three classes so that
each theorem's hypotheses record which it uses: `Extensional`, `Grounded`,
`Constants`.

## 2. `a4` costs six formulae and buys nothing the file asks for

Six of 114 results reach `a4`, and **not one is a conjecture of the TPTP
file**. Five are substantive; the sixth, `MLTStar.grounded`, is the axiom's own
restatement.

* `exists_individual_reachable`
* `not_all_instances_specialize`
* `not_categorizes_self`
* `IsPowertypeOf.ne`
* `Categorizes.ne`

Meanwhile `a4` is the sole reason for the auxiliary theory of sets of types.
Six of the file's 23 axioms — `a4` and its five scaffolding axioms — exist to
state something no conjecture uses.

The axiom does earn its place, elsewhere. Quantifying over predicates rather
than over encoded finite sets makes it one line, and in that form it *derives*
the `typeWellFounded` fact that `mlt_star.als` has to assume separately. Two
assumptions collapse into one.

Its whole yield rests on a single lemma:

> **`not_all_instances_specialize`** — no type has all of its instances
> specializing it.

Such a type would be self-supporting: an instance of an instance of `t` would
again be an instance of `t`, so the class of `t`'s instances would be closed
under instantiation, which is exactly what `a4` forbids. Two shapes of
circularity follow, neither previously recorded: no type is its own Cardelli
powertype (`IsPowertypeOf.ne`), and no type categorizes itself
(`not_categorizes_self`).

## 3. The constants are the load-bearing axiom

`a13`–`a15` reads like notational convenience. It is the widest-reaching
assumption in the theory: 44 of 114 results, against 15 for extensionality and
6 for grounding.

It also has ontological force that had not been drawn out.

> **`exists_individual`** — the mere existence of `cIndividual` forces an
> individual to exist.

If nothing were an individual, nothing would instantiate `cIndividual`; having
no instances, `cIndividual` would itself be an individual — a contradiction.
MLT* cannot be satisfied by a domain of pure types, and this follows from `a13`
with no help from `a4`.

That one forced individual then forces the whole chain
`cIndividual : cFot : cSot`, all three provably distinct
(`iof_cIndividual_cFot`, `iof_cFot_cSot`, `cIndividual_ne_cFot` and siblings).

## 4. The constants *are* the stratification

`cFot` is not merely *a* Cardelli powertype of `cIndividual` — it is *the* one
(`IsPowertypeOf.eq_cFot`), and likewise `cSot` of `cFot`. More strongly:

> **`firstOrderType_iff_specializes_cIndividual`** — being first-order is the
> same condition as specializing `cIndividual`.

with `secondOrderType_iff_specializes_cFot` its analogue. The constants are the
tops of their orders, and `cIndividual_basicType`, `cFot_basicType`,
`cSot_basicType` show they are the first three basic types of `mlt_star.als`.

What climbs the stratification is the powertype, and it climbs by exactly one:

> **`IsPowertypeOf.secondOrderType`** — the Cardelli powertype of a first-order
> type is a *second*-order type.

`powertypeNotFirstOrder` in the TPTP file is the weak shadow of this: it says
only that the powertype is not first-order, not what it is. Underneath sits
`firstOrderType_of_specializes` — order is inherited *downwards* along
specialization — from which specialization provably never crosses orders in
either direction.

## 5. The negative results are as informative as the positive ones

Three things that cannot be proved, each for a reason worth knowing.

**Subordination is not provably irreflexive.** `a4` constrains instantiation
descending, not proper specialization ascending; an infinite strictly ascending
chain of instances satisfies it. If irreflexivity is wanted it needs
stratification or a further axiom.

**`iof` is not provably irreflexive — and should not be.** A universal type
instantiates itself (`IsUniversal.iof_self`). What is elegant is that `a4` is
precisely the weakest well-foundedness condition compatible with that: it
permits self-instantiation at the top while still forcing every type to bottom
out in individuals. A blunter acyclicity axiom would break MLT*.

**The star content is permissive, not mandatory.** The four-element model
contains no universal type and no orderless type at all (`Model.no_universal`,
`Model.no_orderless`). The axioms therefore do not *entail* the phenomena MLT*
was extended to accommodate; they permit them. Establishing that requires
exhibiting a model, which is why it appears in neither existing specification.

## 6. A third formalisation is a differential test on the first two

Both defects found in `tptp/mlt-star.p` surfaced the same way: transcribing
forces a decision the original never had to make.

`a12_subordinationDef` quantified `T4` universally where the paper and
`mlt_star.als` quantify existentially. The error was invisible **because** no
conjecture mentioned subordination — nothing exercised it, so no prover ever
disagreed. It matters: under the universal reading any two instances of `T2`
must share an instance, so a `T2` that disjointly categorizes anything can have
at most one instance.

The formulae of `t1_basetypeUnique` and `t2_powertypeUnique` were interchanged
with respect to their names and comments. That survived because both are true,
so both reports came back green.

Both are now corrected in `tptp/mlt-star.p`.

The methodological point generalises. Because the axioms are typeclasses rather
than global assumptions, a theorem can only use an axiom it names in its own
hypotheses, and `scripts/AxiomAudit.lean` turns "which axioms does this really
need" into a command. Claims like *no conjecture needs `a4`* stop being
editorial and become checkable — and stay checkable as the theory grows.

## 7. Two results the existing specifications state only halves of

> **`categorizes_iff`** — the categorizers of `t` are *exactly* the
> specializations of the Cardelli powertype of `t` that do not have `t` itself
> as an instance.

`t4` is one half of one direction of this.

> **`Partitions.existsUnique`** — every instance of the base type instantiates
> *exactly one* instance of a type that partitions it.

Completeness supplies at least one and disjointness at most one. Both
specifications state the two halves and never draw the conclusion the name has
always promised. Neither result needs any axiom.

---

## Reproducing the figures

```sh
cd lean
lake build
LEAN_PATH=.lake/build/lib/lean lean scripts/AxiomAudit.lean
```

One tab-separated row per declaration: kind, whether it was hand-written,
name, axioms reached, dependencies within `MLTStar`. The counts above are the
`thm` + `src` rows.
