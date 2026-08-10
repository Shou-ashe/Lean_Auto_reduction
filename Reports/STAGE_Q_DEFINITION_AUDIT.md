# Stage Q-A definition and literature audit

Status: **FROZEN FOR Q-A**  
Audit date: 2026-08-06  
Scope: class-level Boolean CSP definitions and the claims that affect the Stage-Q benchmark matrix. No model API was called.

## 1. Audit rule

An `expected` result may enter Stage Q only when all of the following are fixed: the problem is a class rather than one instance; Γ is a finite set of finite Boolean truth tables; clause arity means either “exactly” or “at most” explicitly; repeated variables/literals are either allowed or forbidden explicitly; occurrence counts say whether they count clauses or literal positions; and planarity names the exact graph supplied with the input.

Reading depth below is `F` (full text/theorem inspected), `A` (publisher/arXiv abstract inspected), or `B` (bibliographic metadata only). `B` items may support provenance but not an expected outcome.

## 2. Frozen definitions

- `BooleanRelation(k)` is a finite set of rows in `{0,1}^k`; arity is part of its identity.
- Γ is a finite relation set. An infinite schema such as “all Horn relations” is not a Stage-Q input.
- `CSP(Γ)` is the class of all finite conjunctions of applications of relations in Γ, with existential Boolean assignments.
- The canonical Γ identity is the sorted full truth-table payload. The external identity is SHA-256 over canonical JSON; structural parameters are hashed separately with the Γ identity.
- The six checks are uniform over all relations in Γ: 0-valid, 1-valid, meet-closed (Horn), join-closed (dual-Horn), majority-closed (bijunctive), and ternary-XOR-closed (affine). Γ is tractable when at least one check holds for every member.
- `Planar` means the bipartite variable–clause incidence graph is planar. `Strongly planar` means the literal–clause graph is planar after adding the edge `x—¬x` for every variable, exactly as defined by Dehghan.
- For ordinary 3SAT, “monotone formula” means every clause is all-positive or all-negative. For NAE in this benchmark, `positive` means that negations are absent. The two terms are not interchangeable.
- `E3` means exactly three **distinct** variables per clause. `3SAT-s` means E3SAT with every variable occurring in at most `s` clauses. Repeated literals and 2-clauses define different classes.

## 3. Corrections discovered by Q-A

These findings override the earlier draft matrix.

1. **Binary disequality is still 2-CNF.** `x ≠ y` is `(x ∨ y) ∧ (¬x ∨ ¬y)`. Therefore `CSP({x∨y, x≠y})` is bijunctive and in P; it cannot be an NP-hard Stage-Q target. A hard “2SAT + parity” near miss must use a genuinely non-bijunctive parity relation, for example ternary even parity `x⊕y⊕z=0` together with `x∨y`.
2. **The E3SAT occurrence jump is 3→4, not 2→3.** Tovey states that E3SAT with at most three occurrences per variable is always satisfiable and that the at-most-four variant is NP-complete. The positive case is renamed `q-p-3-4-sat`; the negative control is `(3,3)-SAT`.
3. **Positive NAE occurrence claims depend on clause shape.** Positive NAE-E3SAT with exactly three distinct variables and at most three occurrences is in P. Filho’s adjacent Positive NAE-3SAT-3 hardness construction admits 2-clauses; it is not the same class. The benchmark input must say `E3` and `distinct`.
4. **Planar NAE claims were too broad.** Moret proves general Planar NAE3SAT is in P. The stronger “every instance is satisfiable” statement is frozen only for **positive**, incidence-planar inputs with at least three distinct variables per clause, as stated by Darmann–Döcker–Dorn from Pilz’s construction. General signed Planar NAE remains a P witness, not an always-yes witness.
5. **Kratochvíl 1994 is not admitted as the bounded-occurrence planar-3SAT source.** The inspected metadata identifies a special planar satisfiability problem used for intersection-graph hardness, but did not verify the draft’s exact “planar 3SAT + every variable at most three times” sentence. That benchmark restriction stays deferred.

## 4. Critical claim audit

| Claim | Depth | Expected impact | Conclusion |
| --- | --- | --- | --- |
| Schaefer dichotomy for finite Boolean relation sets | A | all Γ cases | Verified at theorem/metadata level: every generalized Boolean satisfiability problem is polynomial-time decidable or NP-complete. The implementation uses the standard six closure tests. [Schaefer 1978](https://doi.org/10.1145/800133.804350) |
| Tovey bounded occurrence threshold | A + author summary | `(3,s)` pair | Correct threshold is E3SAT `s≤3` always satisfiable, `s=4` NP-complete. [Publisher record](https://www.sciencedirect.com/science/article/pii/0166218X84900817), [author publication summary](https://sites.gatech.edu/craig-tovey/publications/) |
| KST general occurrence jump | A | general `(k,s)` wording | Verified only in threshold form: for every `k≥3` a threshold `f(k)` separates trivial from NP-complete. Use Tovey for the concrete `k=3` threshold. [KST 1993](https://doi.org/10.1137/0222015) |
| Pilz “monotone” convention | F/A | planar near misses | In the paper, a monotone 3SAT clause is all-positive or all-negative; it does **not** mean positive-only. Pilz also proves the exact-three-distinct monotone planar formula is satisfiable. [DMTCS article](https://doi.org/10.23638/DMTCS-21-3-18) |
| Positive planar NAE always satisfiable | F | `q-n-planar-nae3` | Verified only with positive clauses and at least three distinct variables per clause. [DDD 2024, lines summarized on arXiv](https://arxiv.org/abs/2412.03395) |
| General planar NAE3SAT | A | signed planar negative control | Verified in P, via reduction to planar Simple MaxCut; not frozen as universally satisfiable. [Moret 1988](https://doi.org/10.1145/49097.49099) |
| Strongly planar definition and complexity | F | strongly-planar control | Definition is the literal/clause graph plus `x—¬x`; the NAE problem is in P. The restricted positive planar problem with preassigned variables is a different NP-complete class. [Dehghan](https://doi.org/10.1007/s10878-015-9894-6) |
| Positive NAE-E3SAT ≤3 occurrences | F + later primary paper | occurrence near miss | P only for exactly three distinct variables per clause. The later paper explicitly cites Filho Thm. 3.3.2 for this boundary. [DDD 2024](https://arxiv.org/abs/2412.03395), [Filho thesis](https://erikdemaine.org/theses/ifilho.pdf) |
| Positive NAE-3SAT-3 allowing 2-clauses | F | mutation control | NP-complete in Filho Thm. 3.4.1. This is the definition trap paired with the E3/P case. [Filho thesis](https://erikdemaine.org/theses/ifilho.pdf) |
| Positive linear NAE-E4 | F | Q-B hard target | Verified NP-complete with exactly four occurrences and linearity. [Darmann–Döcker 2020](https://arxiv.org/abs/1908.04198) |
| Positive linear k-disjoint NAE-Ek | F | partition cases | `k≥4` NP-complete; `k≤3` in P; `k∈{1,2}` always satisfiable. [DDD 2024](https://arxiv.org/abs/2412.03395) |
| Linear positive NAE / XSAT | A | Q-B source provenance | NP-completeness of monotone linear NAE-SAT and XSAT verified at abstract level. [Porschen et al.](https://doi.org/10.1016/j.dam.2013.10.030) |
| `CSP({x∨y,x≠y})` NP-complete | truth-table audit | removes positive case | Rejected. Both relations are bijunctive; the language is 2-CNF. No gadget should be authored for this target. |
| Kratochvíl 1994 exact bounded planar sentence | B/A | deferred | Not verified; no expected outcome may depend on the draft sentence. [Article record](https://dblp.org/rec/journals/dam/Kratochvil94) |

## 5. Complete bibliography ledger (§2.9)

| # | Source | Depth | Affects current expected? | Audit disposition |
| ---: | --- | :---: | :---: | --- |
| 1 | Schaefer 1978, DOI 10.1145/800133.804350 | A | yes | dichotomy retained; six-class implementation required |
| 2 | Cook 1971; Karp 1972; Garey–Johnson 1979 | B | baseline only | existing Stage-P baseline; no new Q-A claim admitted |
| 3 | Tovey 1984, DOI 10.1016/0166-218X(84)90081-7 | A | yes | draft corrected to `(3,3)` trivial / `(3,4)` NPC |
| 4 | Kratochvíl–Savický–Tuza 1993, DOI 10.1137/0222015 | A | yes | general threshold retained; concrete `k=3` result delegated to Tovey |
| 5 | Lichtenstein 1982, DOI 10.1137/0211025 | F excerpt | yes | incidence-planar SAT hardness retained |
| 6 | Kratochvíl 1994, DAM 52:233–252 | A/B | no | exact draft restriction deferred |
| 7 | Pilz 2019, DOI 10.23638/DMTCS-21-3-18 | F | yes | monotone convention and positive-planar consequence pinned |
| 8 | Moret 1988, DOI 10.1145/49097.49099 | A | yes | general planar NAE is in P; no general always-yes claim |
| 9 | Dyer–Frieze 1986, J. Algorithms 7:174–184 | B | no in Q-A | planar 1-in-3 route remains Q-B and needs theorem-level reread |
| 10 | Moore–Robson 2001, DOI 10.1007/s00454-001-0047-6 | B | no in Q-A | gadget route deferred to Q-B |
| 11 | Darmann–Döcker 2020, arXiv:1908.04198 | F | yes | positive linear NAE-E4 retained |
| 12 | Darmann–Döcker–Dorn 2024, arXiv:2412.03395 | F | yes | k-partition dichotomy and positive-planar statement retained |
| 13 | Kratochvíl–Tuza 2002, J. Algorithms 45:40–54 | B | no in Q-A | NAE-SAT(2,3) occurrence expected deferred |
| 14 | Dehghan–Sadeghi–Ahadi 2015, DOI 10.1007/s00373-014-1446-9 | B | no in Q-A | application provenance only |
| 15 | Filho 2019 thesis | F | yes | E3/distinct-vs-2-clause distinction added |
| 16 | Porschen et al. 2014, DOI 10.1016/j.dam.2013.10.030 | A | yes | linear positive NAE/XSAT hardness retained |
| 17 | Dehghan, DOI 10.1007/s10878-015-9894-6 | F | yes | strongly-planar definition and P status retained |
| 18 | Wu 2015, JCO 32(1):293–298 | B | no | not used; Dehghan/Moret P result controls expected |
| 19 | Henning–Yeo 2018, DOI 10.1016/j.disc.2018.05.002 | A | no in Q-A | hypergraph side result recorded, no current expected |
| 20 | Hasan–Mondal–Rahman 2022, TCS 917:81–93 | B | no | stretch material only |
| 21 | Li–Spirkl 2023, DOI 10.1016/j.disc.2023.113342 | A | no in Q-A | matching-number dichotomy deferred to structural stage |
| 22 | Lewis 1979, Math. Systems Theory 13:45–53 | B | no | Post-lattice background only |
| 23 | Creignou–Khanna–Sudan 2001 | B | no | modern classification background only |
| 24 | Creignou–Vollmer 2008, DOI 10.1007/978-3-540-92800-3_2 | B | no | co-clone stretch only |
| 25 | Schnoor–Schnoor 2008 | B | no | partial-polymorphism stretch only |
| 26 | Du–Ko–Wang 2002 | B | no | strongly-planar 3SAT provenance; not used for NAE expected |
| 27 | Ahadi et al. 2012, IPL 112:109–112 | B | no | application provenance only |
| 28 | Garey–Johnson–Stockmeyer 1976, TCS 1:237–267 | B | no | planar graph baseline only |
| 29 | Papadimitriou–Yannakakis 1991, JCSS 43:425–440 | B | no | optimization/APX background only |
| 30 | Bulatov 2017; Zhuk 2020 | B | no | finite-domain future work, outside Boolean Q-A |
| 31 | Hell–Nešetřil 1990, JCTB 48:92–110 | B | no | graph-H-coloring analogy only |

## 6. Implementation-to-audit trace

- Python: `agent/hardness/boolean_csp_classes.py` implements canonical finite tables, SHA-256 Γ/class fingerprints, all six closure checks, infinite-Γ rejection, and run-local P/NPC single registration.
- Python: `agent/hardness/in_p.py` implements the exact `prove_in_p` evidence gate and a concrete Horn least-model/forward-chaining solver. Its finite Horn implication basis is derived from each truth table.
- Python: `agent/hardness/stage_q_contract.py` and `stage_q_artifact.py` keep `prove_in_p` in a separate versioned request/finish ABI and Lean emitter; the frozen benchmark-v1 objective set and core artifact emitter remain unchanged.
- Lean: `ComplexityReduction.Domain.BooleanCSP` defines relation fingerprints, finite Γ, `CSP(Γ)` as a class-level `PresentedProblem`, six class predicates, and a decider with reflection theorems.
- Lean: `ComplexityReduction.Certificate.DeterministicP` binds one exact `PolyProg`, compiler-derived direct-TM polynomial time, and the exact decision predicate.
- Lean: `ComplexityReduction.Protocol.InP` is a new v1 protocol and leaves the frozen `AutoReductionRequest` ABI unchanged.
- Lean: 0-valid and 1-valid Γ have complete constant-program certificates. Horn evidence is admitted only through an exact program plus correctness proof; Python supplies the concrete algorithm, while Lean model authoring must still elaborate the corresponding program/proof before capability publication.

## 7. Gate decision

Q-A may close. Q-B must use the corrected `(3,4)` occurrence target and ternary parity target, and must encode `E3/distinct` on the positive NAE ≤3-occurrence negative control. The unverified NAE-SAT(2,3) occurrence positive case is replaced by the exact positive-NAE/3-uniform-Set-Splitting representation isomorphism. The deferred Kratochvíl 1994, NAE-SAT(2,3) occurrence, planar 1-in-3, and direct 1-in-3 bounded-occurrence claims may not determine an expected outcome until theorem-level reread.
