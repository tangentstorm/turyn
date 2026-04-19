# math-ideas.md — The Turyn Symposium

A gedanken conference. Fifty mathematicians, from Fermat to Scholze, are
locked in a room with a whiteboard, a coffee urn, and a one-page brief:

> Find four `±1` sequences `(X, Y, Z, W)` of lengths `(n, n, n, n-1)` with
>
>     N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) = 0   for all s ∈ [1, n-1]
>
> equivalently in frequency,
>
>     |X(ω)|² + |Y(ω)|² + 2|Z(ω)|² + 2|W(ω)|² = 6n − 2   ∀ω.
>
> Open cases include n ∈ {28, 30, 32, 36, 38, 46, 48, 50, 52, 54, 56}.
> TT(56) yields a Hadamard matrix of order 668. Go.

Ideas are numbered globally so we can count. Each idea is tagged with the
mathematician who proposed it (in character). Conversational threads
appear as indented asides between sections.

---

## Part I — The physicists of arithmetic

### 1. Pierre de Fermat

> "I have a truly marvelous proof which this margin is too small to contain."

1. **Infinite descent on Turyn orbits.** Assume a Turyn tuple exists at
   length `n`. Use the BDKR canonical form plus a weight function
   (e.g. total positive mass `#(+1) − #(-1)`) to descend to a smaller
   invariant. If no base case exists, contradiction — i.e. use descent
   as an infeasibility certificate for open `n`.
2. **Fermat's method of adequality on the relaxation.** Treat `±1` as
   the limit of `tanh(βu)`; write the autocorrelation constraints as
   real analytic equations, set derivatives to zero, and look for
   "near-solutions" as β → ∞.
3. **Little theorem over F_p.** Reduce the autocorrelation polynomial
   identity mod small primes p; a Turyn tuple must survive every
   congruence. Use it as a sieve on sum-tuples.

### 2. René Descartes

4. **Cartesian relaxation.** Embed `±1^{4n-1}` in `R^{4n-1}` as the
   vertices of a hypercube. The autocorrelation constraints are
   quadratic. Solve the relaxed quadratic system on the ball, then
   round. ADMM or projected gradient on the sphere works out of the
   box.
5. **Rule of signs, inverted.** Descartes' rule bounds real roots of
   polynomials by sign changes. The `±1` sequence *is* a sign pattern.
   Construct a polynomial whose sign pattern is forced by the
   autocorrelation identity.
6. **Mind–body duality on X vs Y.** The symmetry `X ↔ Y` is a natural
   involution (rule T4 in BDKR). Quotient the search space by it
   first; then search only `X + Y` and `X − Y` pairs (which lie in
   `{−2, 0, 2}^n`).

### 3. Isaac Newton

> "If I have seen further, it is by standing on the shoulders of Sylvester."

7. **Newton's identities.** Power sums `p_k = Σ x_i^k` over the
   sequences are trivial (all ±1 → p_k ∈ {±n}), but power sums of
   *products* `x_i x_{i+s}` are exactly the autocorrelations
   `N_X(s)`. Newton's identities relate these to elementary symmetric
   functions of the `x_i x_{i+s}` — potentially new constraints.
8. **Fluxions (gradient flow) on the loss.** Define `L(X,Y,Z,W) =
   Σ_s (N_X + N_Y + 2N_Z + 2N_W)²`. Run continuous-time gradient
   flow with a penalty keeping coordinates near `±1`. Newton would
   have loved the geometry of the flow's fixed points.
9. **Newton polygon of the zeta-autocorrelation.** Form
   `Z_X(t) = Σ N_X(s) t^s`; Newton's polygon of the polynomial `Z_X
   + Z_Y + 2Z_Z + 2Z_W` must be trivial for Turyn tuples. Use this as
   a combinatorial certificate.

### 4. Leonhard Euler

10. **Euler product over primes.** Let `χ` range over Dirichlet
    characters of conductor dividing `2n`. The sum
    `Σ_χ |X̂(χ)|² = n · (something)` opens a character-theoretic
    accounting identity. Exploit multiplicativity.
11. **Euler's pentagonal number theorem analogue.** Generating
    function `∏(1 − q^k)` has miraculous cancellation. Form
    `∏_s (1 − q^s)^{N_X(s)}` and seek miraculous identities when the
    exponents satisfy the Turyn relation.
12. **Latin squares.** Euler loved orthogonal Latin squares.
    Turyn-type sequences and orthogonal designs are close cousins.
    Look for an OD(4n; n, n, 2n, 2n−2) and a reverse-engineering of
    its first rows to produce `(X, Y, Z, W)`.
13. **Euler–Maclaurin on autocorrelations.** Replace the discrete
    sum `N_X(s)` by an integral + correction terms. The corrections
    might isolate solvable sub-problems.

### 5. Carl Friedrich Gauss

> "Mathematics is the queen of the sciences, and arithmetic the queen of mathematics."

14. **Cyclotomic embedding.** Associate to `X` the element
    `X(ζ) = Σ x_i ζ^i ∈ Z[ζ_m]`. The autocorrelation identity becomes
    `|X(ζ)|² + |Y(ζ)|² + 2|Z(ζ)|² + 2|W(ζ)|² = 6n − 2` at each
    primitive `m`-th root `ζ`. For chosen `m` use known factorisation
    of `6n − 2` in the ring of integers of `Q(ζ_m)`.
15. **Gauss sums for Paley-like Z.** Take `Z_i = (i | p)` (Legendre
    symbol) for suitable prime `p`; `|Z(ω)|²` is then governed by
    Gauss sums. Search only over choices of `Z` in the
    quadratic-residue family; let `X`, `Y`, `W` compensate.
16. **Gauss's pigeonhole.** Among `2^n` sequences there are only
    poly(n) distinct autocorrelation vectors (bounded by `n^(2n)`).
    By pigeonhole, *many* collisions — enumerate by autocorrelation
    signature and merge. Hash by autocorrelation and stop at the
    first quadruple.
17. **Ternary Gauss reduction.** View the autocorrelation vector
    `(N_X + N_Y, N_Z, N_W) ∈ Z^{3(n-1)}` as a lattice point; reduce
    using Gauss-type lattice reduction to a short form, then
    back-substitute.

### 6. Bernhard Riemann

18. **Meromorphic continuation of autocorrelation.** Define
    `ζ_X(w) = Σ_{s≥1} N_X(s) / s^w`. The pole structure encodes
    cancellations. Turyn means `ζ_X + ζ_Y + 2ζ_Z + 2ζ_W ≡ 0`
    identically — look for an analytic obstruction.
19. **Riemann surface of (Z, W).** Parameterise Z, W by a single
    complex variable via generating functions; the locus
    `|Z(ω)|² + |W(ω)|² ≤ 3n − 1` cuts out a Riemann surface whose
    genus controls how many `(Z, W)` pairs survive.
20. **Hypothesis-style bound.** Assume the analogue of RH for the
    autocorrelation L-series; the resulting square-root cancellation
    bound would imply `max_ω |X(ω)| = O(√(n log n))`. Use this to
    pre-filter candidate boundaries.

> *Gauss, leaning over Riemann's shoulder:* "My boy, your zeta works, but
> for this problem I'd just count the quadratic residues mod 4n+3 and
> be done."
> *Riemann:* "Teacher, the pole at w = 1 tells us more than residues
> alone."
> *Turyn, from the back:* "You're both right — and both wasting time
> until n ≡ 1 (mod 3) is ruled out."

### 7. David Hilbert

> "Wir müssen wissen — wir werden wissen."

21. **Hilbert's 17th problem connection.** The nonnegative quantity
    `Σ_ω (|X(ω)|² + |Y(ω)|² + 2|Z(ω)|² + 2|W(ω)|² − (6n−2))²` is a
    trigonometric polynomial ≥ 0. By Hilbert's SOS theorem on the
    torus it is a sum of squares of trig polynomials — each SOS
    decomposition is a system of quadratic constraints.
22. **Positivstellensatz.** If no Turyn tuple exists at `n`, there is
    a polynomial identity proving the empty-set statement. Search
    for an SOS certificate with degree bound 4 or 6 — feasible at
    small `n`.
23. **Hilbert basis theorem.** The ideal generated by all
    autocorrelation identities in `R[x_1, …, x_{4n-1}]` is finitely
    generated; compute a minimal generating set and use it as a
    redundancy-free constraint list.
24. **Hilbert cube combinatorics.** The solution set is a subset of
    the Hilbert cube `{±1}^{4n-1}`; use its symmetric group action
    and a Hilbert cube lemma to produce a monochromatic sub-cube of
    solutions.

### 8. Henri Poincaré

25. **Topology of the solution variety.** Let `V_n ⊂ R^{4n-1}` be
    the real variety cut out by the autocorrelation equations plus
    `x_i² = 1`. Compute Euler characteristic and Betti numbers — a
    nonzero Euler characteristic at `n=56` would imply TT(56)
    exists.
26. **Poincaré recurrence on the shift.** The Bernoulli shift on
    `{±1}^Z` is measure-preserving; recurrence says periodic orbits
    of length `n` of the shift, filtered by the autocorrelation
    constraint, recur. Use this to motivate random restart with
    memory.
27. **Qualitative dynamical systems view.** The SAT search is a flow
    on state space; identify its limit cycles and repellors. Inject
    perturbation exactly along repelling directions.

### 9. Emmy Noether

> "If one proves the equality of two numbers `a` and `b` by showing first
> that `a ≤ b` and then that `a ≥ b`, it is unfair; one should instead
> show that they are really equal by disclosing the inner ground for
> their equality."

28. **Hidden symmetry ⇒ conservation law.** The spectral identity
    `|X(ω)|² + |Y(ω)|² + 2|Z(ω)|² + 2|W(ω)|² = 6n − 2` is a
    *conservation law*. By Noether, there is an underlying continuous
    symmetry. Guess: it's an `O(1) × O(1) × Sp(1)` compact group
    action on the generating functions. Find the Noether current;
    any violation of it rules out tuples instantly.
29. **Noetherian module on autocorrelations.** The module of
    autocorrelation functions over `Z[C_n]` is Noetherian; its
    composition series identifies primary solvable sub-problems.
30. **Galois/Noether closure of the tuple.** The Galois closure of
    the field generated by all roots of the autocorrelation
    polynomial has known degree bounds; candidates outside the
    closure are rejected automatically.

### 10. Srinivasa Ramanujan

> *scribbles furiously, hands Hardy a card*

31. **Mock-theta style generating function.** Define
    `f(q) = Σ_{(X,Y,Z,W) ∈ Turyn} q^{Σ i·x_i}`. Conjecture `f(q)` has
    modular behaviour; verify the first 10 coefficients
    experimentally and guess a closed form.
32. **Ramanujan sums.** `N_X(s) = Σ_d | s c_d(X)` where `c_d` is a
    Ramanujan sum restricted to `X`. Sparsify the autocorrelation
    constraints using Möbius inversion.
33. **Taxicab-style enumeration of sum-tuples.** `x² + y² + 2z² + 2w²
    = 6n − 2` has a Ramanujan-like closed-form count via theta
    functions. Use it to *pre-count* per-`n` how many sum-tuples
    exist; it's a tight bound for Phase A.
34. **Intuitive guess of a family.** Scan known TT(n) for n ≤ 44 and
    spot Ramanujan-style patterns: position of +1s, agreement
    counts, periods of half-sequences. *Pattern first, proof later.*

> *Hardy, reading the card:* "These identities have no right to be true.
> Therefore they must be."
> *Ramanujan, smiling:* "Mrs. Turyn told me."

### 11. Kurt Gödel

35. **Formal verification in Lean/Coq.** Mechanise the autocorrelation
    identity and the BDKR canonical form. This does *not* help find
    solutions but it pays later: a Lean-checked TT(56) is the
    gold-standard publication.
36. **Compactness of first-order theory.** If TT(n) exists for
    arbitrarily large n, the compactness theorem gives an infinite
    `±1^ω` quadruple satisfying all finite autocorrelation
    identities. Identify it; extract periodic sections.
37. **Arithmetical hierarchy placement.** "TT(n) exists" is a `Σ_1`
    statement; "TT(n) does not exist" is `Π_1`. For small `n`, both
    are decidable. For the limit statement "TT(n) exists for
    infinitely many n", placement in the hierarchy guides strategy.

### 12. Alan Turing

38. **Bombe-style elimination.** Use the Turyn canonical form as a
    "menu" that tests many rotor positions in parallel; each XY
    solve is one Bombe cycle. Implementation: cluster (Z,W) pairs
    that share many common reduced clauses and solve jointly.
39. **Universal neural net heuristic.** Train a small transformer
    on `(boundary → SAT outcome)` for n ≤ 30 and use it as a
    priority function for n ≥ 40. A cheap experiment: grad-boosted
    trees on MDD features predicting XY-SAT/UNSAT.
40. **Turing pattern on the sequence.** Reaction-diffusion on the
    1-D lattice with the autocorrelation as the interaction kernel.
    Stable Turing patterns = candidate Turyn sequences.

### 13. John von Neumann

> "Young man, in mathematics you don't understand things. You just get used to them."

41. **Minimax linear programming.** Relax `x_i² = 1` to `x_i ∈
    [-1, 1]`; solve the max-entropy LP with the autocorrelation
    equality constraints. The dual gives a Lagrangian certificate
    of infeasibility when UNSAT.
42. **Random matrix theory.** Treat the autocorrelation operator as
    a random `n × n` circulant. Its spectral distribution converges
    to a known semicircle-like law. Turyn tuples are outliers;
    characterise the outlier rate.
43. **Stored-program pragmatism.** Stop philosophising and allocate
    more cores. Von Neumann would point out the pipeline is already
    well-tuned; the bottleneck is wall-clock. Run 1024 machines in
    parallel.
44. **Game-theoretic XY vs ZW.** Model the search as a two-player
    zero-sum game between "boundary chooser" and "middle completer".
    Mixed-strategy Nash tells us the optimal sampling distribution
    over MDD paths — plug into the LCG replacement.

### 14. Évariste Galois

45. **Galois group of the autocorrelation polynomial.** Let `P(t) =
    Σ N_X(s) t^s`. Its Galois group over `Q` is constrained by the
    Turyn identity. Enumerate only `X` whose `P` has prescribed
    Galois group.
46. **Solvable-by-radicals sub-family.** Look for `Z` constructed
    from subgroups of `(Z/pZ)^*`; these have solvable Galois
    structure and are cheap to parameterise.
47. **Galois cohomology obstruction.** The Turyn equation might
    have a local-global obstruction classified by `H^1(Gal(Q̄/Q),
    …)`. A non-trivial class rules out solutions at that `n`.

### 15. Niels Henrik Abel

48. **Abelian summation.** `Σ s · N_X(s) = (Σ i x_i)² − n`. The
    weighted Turyn identity gives another invariant:
    `(Σ i x_i)² + (Σ i y_i)² + 2(Σ i z_i)² + 2(Σ i w_i)² =
    (6n − 2) n + correction`. Use as a second-order sieve.
49. **Abel's impossibility theorem.** If TT(n) provably does not
    exist for some n, give an impossibility proof in the style of
    Abel: exhibit a radical tower that any Turyn solution would
    have to inhabit, then show no such tower is consistent with ±1.

### 16. Georg Cantor

50. **Diagonalisation construction.** Enumerate candidate X
    sequences; for each, construct Y to disagree at the diagonal
    position — forcing the final Y to miss every enumerated
    candidate. Reverse use: diagonal *obstruction* proofs.
51. **Cardinality of the symmetry class.** The BDKR orbit has size
    ≤ 1024. Cantor's bijection-counting applied at the level of
    orbits may reveal hidden structure (e.g. orbit sizes divide
    1024 in a predictable way per n mod 8).

## Part II — Combinatorics, probability, and gigatons of data

### 17. Paul Erdős

> "The SF will let me look up a Turyn tuple in The Book — if God allows."

52. **Probabilistic method.** Random `(X, Y, Z, W) ∈ {±1}^{4n-1}`
    has `E[N_X(s) + N_Y(s) + 2N_Z(s) + 2N_W(s)] = 0` by symmetry;
    second moment `O(n)`. A Lovász Local Lemma argument on the
    `(n-1)` autocorrelation constraints — with dependency graph of
    bounded degree — gives `P(all satisfied) > 0` for large enough
    n. Prove the LLL hypothesis; constructive LLL gives a
    polynomial-time finder.
53. **Deletion method.** Start from a random tuple; greedily flip
    bits that decrease `Σ_s (…)²`. Track the time to fix. Expected
    $1000 for a proof that runs in sub-exponential time.
54. **Ramsey-type statement.** For large `n`, every `±1^{4n-1}`
    tuple must either contain a Turyn sub-pattern or avoid it
    heavily. Quantify; use Ramsey numbers as lower bounds.
55. **Erdős on open problems.** Post each open `n` (28, 30, 32, 36,
    …) as a separate bounty problem; independent attacks likely
    break them in different orders.

### 18. Andrey Kolmogorov

56. **Low K-complexity search.** TT(n) sequences published so far
    have low Kolmogorov complexity (short descriptions — palindromes,
    near-periodicities). Restrict search to sequences with
    description length `≤ c log n` bits for small `c`; re-run for
    each `n`. A computational pre-filter: enumerate LFSR-like
    generators and test.
57. **Randomness defects.** A Turyn `X` has specific defects from
    random: zero autocorrelation-sum residue. Use these as tests of
    pseudorandomness; enumerate sequences that fail exactly the
    Turyn defect test.
58. **Measure-theoretic density.** Establish `density_n =
    |Turyn(n)| / 2^{4n-1}`. If `density_n > 0` infinitely often,
    probabilistic methods apply; if density decays like `2^{-cn²}`,
    any finder must exploit structure.
59. **Kolmogorov-Arnold representation.** Any continuous function of
    many variables is a superposition of single-variable functions.
    Maybe the Turyn indicator is such — express it as a sum of
    low-arity functions and optimise.

### 19. John Horton Conway

60. **Game of Life on the tuple.** Map each position to a cell;
    evolution rule = "flip if autocorrelation-violation gradient is
    negative". Look for stable still-lifes and oscillators — Turyn
    tuples are *stills*.
61. **Surreal embedding.** Embed partial Turyn solutions into a
    surreal game tree; evaluate positions by Conway's temperature
    theory; explore hottest branches first.
62. **Look-and-say on autocorrelations.** Iterate the map `N_X →
    histogram of N_X`; examine its orbit. Turyn tuples have a
    degenerate orbit (all-zero).
63. **ATLAS of finite groups.** The Turyn symmetry group (BDKR
    T1..T4) is a Coxeter-type extension of `(Z/2)^8 ⋊ S_2`. Look up
    its character table and use irrep-space projections to split
    the SAT problem.

### 20. Terence Tao

64. **Additive combinatorics.** View `X` as ±1-valued function on
    `Z/nZ`; `N_X(s)` is the convolution coefficient. Apply
    Plancherel + Bessel to get
    `Σ_ω |X(ω)|^4 ≤ (6n − 2) · max_ω |X(ω)|²`. Combined with
    `Σ_ω |X(ω)|² = n`, this gives a moment-method lower bound on
    `max_ω |X(ω)|` — a *spectral flatness* floor.
65. **Restriction-style bound.** The restriction theorem on `Z/nZ`
    gives `||X̂||_q ≲ ||X||_p` for specific `(p, q)`; apply to X, Y
    to rule out boundaries whose partial restriction norm is too
    large.
66. **Ergodic Szemerédi-type approach.** The set of `i` with
    `x_i = +1` has density 1/2 ± O(n^{-1/2}); Szemerédi guarantees
    a long arithmetic progression inside it. Use AP structure as a
    search template.
67. **Polynomial method.** Parametrise `X = sign(p(i))` for low-
    degree `p`; the autocorrelation identity becomes a polynomial
    inequality in the coefficients of `p`. Search over degree-`d`
    polynomials for small `d`.

### 21. H. S. M. Coxeter

68. **Reflection-group orbit enumeration.** The BDKR T-group is
    generated by reflections; it sits inside the hyperoctahedral
    group `B_{4n-1}` as a rank-`r` sub-Coxeter system. Use Coxeter
    combinatorics (short elements) to enumerate canonical
    representatives in increasing length.
69. **Root-system basis.** Express `(X, Y, Z, W)` in the standard
    basis of the root system; autocorrelations become pairings
    `(α, β)` for roots α, β. Turyn tuples are roots of a
    sub-system; search only that sub-system.
70. **Regular polytopes as priors.** The vertices of the
    hyperoctahedron `β_n` are `±e_i`; Turyn tuples lie on specific
    facets. Coxeter-catalogue possible facets and iterate.

### 22. Alexander Grothendieck

71. **Scheme of solutions.** `X_n = Spec Z[x_1..,y_1..,z_1..,w_1..]
    / (x_i² − 1, autocorrelation identities)`. Study `X_n(F_p)` for
    small primes; count via étale cohomology.
72. **Categorification.** Replace the set of Turyn tuples by a
    groupoid (tuples and symmetries). Groupoid cardinality gives
    the orbit count directly.
73. **Rising sea metaphor.** Instead of hammering at one `n`,
    reformulate the *class* of all `n` in a richer category (e.g.
    the category of group rings) and let the right abstraction
    make the problem obvious.
74. **Topos of presheaves on canonical forms.** Overkill but
    principled. The site of BDKR orbits forms a small category;
    the topos of presheaves gives an internal logic where
    "Turyn-ness" is a subobject classifier assertion.

> *Grothendieck at the chalkboard:* "The right question is not 'does
> TT(56) exist?' but 'what is the functor that sends n to the groupoid
> of Turyn tuples?'"
> *Erdős, sotto voce:* "And what is its value at 56?"

## Part III — Analysts, fields, and continuous mathematics

### 23. James Clerk Maxwell

75. **Electromagnetic dual.** Interpret `X, Y, Z, W` as four polarised
    antenna feed patterns. The Turyn identity is constant
    radiated-power isotropy. Adapt phased-array synthesis
    algorithms (Dolph–Chebyshev) to produce candidate sequences.
76. **Stress-energy tensor.** Form a 4×4 "Turyn tensor" of
    autocorrelation functions; its trace is the Turyn invariant.
    Decompose into traceless parts; each irreducible component
    must vanish separately. Gives independent constraint blocks.
77. **Standing-wave coupling.** Maxwell's equations support
    non-radiating sources; find ±1 non-radiating sources on a
    length-n lattice, they correspond to Turyn components.

### 24. Joseph Fourier

78. **DTFT is the truth.** Transform everything; the Turyn identity
    becomes a pointwise constraint in frequency. Over-enforce at
    many frequencies (θ ≫ n), which the code already does via
    `SpectralConstraint` — push θ to 8n and re-benchmark.
79. **Partial Fourier sum method.** Truncate `X̂` to its first `k`
    frequencies; enforce the truncated Turyn identity exactly.
    Rejects sequences whose low-frequency energy is misdistributed
    before any SAT work.
80. **Fourier convolution theorem as a SAT constraint.** The
    autocorrelation in time is the power spectrum in frequency;
    encode the (integer-valued) power spectrum constraints directly
    via a radix-2 combinator of XOR/majority gates.

### 25. Pierre-Simon Laplace

81. **Laplace transform (z-transform).** `X(z) = Σ x_i z^i`. The
    Turyn identity is `X(z) X(1/z) + Y(z) Y(1/z) + 2Z(z) Z(1/z) +
    2W(z) W(1/z) = 6n − 2`. Factor over `Z[z]`; look for
    factorisation patterns.
82. **Laplace determinantal expansion.** The `4n × 4n` matrix of
    pairwise shifts has a determinant; compute or bound it. Tight
    bounds eliminate boundaries.
83. **Celestial mechanics analogy.** Treat the 4 sequences as
    four-body orbits in a 1-D time; Laplacian stability of the
    "orbit" (no secular growth of autocorrelation) corresponds to
    Turyn.

### 26. Joseph-Louis Lagrange

84. **Lagrangian relaxation.** Introduce multipliers `λ_s` for each
    autocorrelation constraint; maximise `inf_x L(x, λ)` over
    `x ∈ {±1}^{4n-1}`. Good `λ` give certificates (dual bounds).
85. **Four-square theorem.** `x² + y² + 2z² + 2w² = 6n − 2` — apply
    Lagrange's four-square theorem to enumerate integer solutions.
    Many symmetries reduce the tuple count below current counts.
86. **Variational principle.** The Turyn tuple minimises
    `||autocorr||²` over the hypercube. Lagrange-Euler equations
    give critical-point conditions; use projected Newton on them.

### 27. Augustin-Louis Cauchy

87. **Contour integration of character sums.** Express `|X(ω)|²` as
    a contour integral; shift contours to pick up residues that
    bound the maximum.
88. **Cauchy–Schwarz funnel.** `|N_X(s)|² ≤ n²`; refinements via
    Cauchy–Schwarz on sub-sums give tighter per-lag bounds. Encode
    as SAT constraints.
89. **Cauchy determinantal identity.** Use Cauchy's identity to
    express products of autocorrelations as determinants; compute
    once and cache.

### 28. Henri Lebesgue

90. **Measure concentration.** On `{±1}^{4n-1}` with uniform
    measure, the quantity `Σ_s (…)²` concentrates around its
    expectation `O(n)`. Turyn tuples are in the extreme tail; use
    isoperimetry to bound their count.
91. **Dominated convergence on sum-tuples.** The number of sum-
    tuples satisfying `x² + y² + 2z² + 2w² = 6n − 2` is governed by
    a theta-function; Lebesgue's DCT lets us swap limits when
    taking `n → ∞` for asymptotic density.

### 29. G. H. Hardy

> "Pure mathematics, of course, is practically always useless."

92. **Circle method.** Express `|Turyn(n)|` as a contour integral
    around `|z| = 1` of a generating function; split into major
    and minor arcs. Major arcs give the main term; minor arcs must
    be bounded by character-sum estimates.
93. **Hardy–Littlewood asymptotic.** Conjecture:
    `|Turyn(n)| ∼ C · 2^{4n-1} · n^{-(n-1)/2}` (Poisson heuristic
    with n−1 nontrivial constraints). Verify on known data.
94. **Bad-sequence count.** Show that the number of `X` with
    `max_ω |X(ω)|² > c·n` decays faster than `2^{-δn}`; this
    tightens any search to "flat" X.

### 30. J. E. Littlewood

95. **Littlewood flatness conjecture.** "Does there exist a ±1
    sequence with `|X(ω)|` uniformly close to √n?" Turyn sub-
    sequences are *required* to be flat-ish. The Rudin–Shapiro
    construction gives a factor `√2`; does it help here?
96. **Littlewood's 4/3 bound.** `||X̂||_4 ≥ n^{1/4} ||X̂||_2^{1/2}`.
    Apply to the sum `|X(ω)|⁴ + …` for tightening.
97. **Littlewood polynomials.** `X` is literally a Littlewood
    polynomial. Use known extremal results: Erdős–Kahane, Rudin,
    and Borwein–Mossinghoff's catalogues.

### 31. Andrew Wiles

98. **Modularity.** Associate to each Turyn tuple a Galois
    representation; conjecture modularity of the L-series and
    exploit Hecke eigenvalue relations to narrow down `(Z, W)`
    families.
99. **Taylor–Wiles patching.** Patch approximate solutions at each
    prime to produce a global Turyn tuple. (Far-fetched but the
    patching philosophy — build consistency level by level — maps
    naturally onto MDD levels.)

### 32. Pierre Deligne

100. **Weil conjectures and character-sum bounds.** For `X = (i|p)`
     (Paley-like), `|X(ω)|² ≤ p + 1` by Weil's bound. Use to prove
     spectral-flatness for *entire families* of sequences at once.
101. **ℓ-adic cohomology count.** Count `|X_n(F_p)|` via étale
     Euler characteristic; `|X_n(Z)|` inherits a lower bound when
     the `F_p` count is positive and Hasse-type obstructions
     vanish.

### 33. Jean-Pierre Serre

102. **p-adic lifting.** Lift solutions from `F_2` or `F_3` to
     `Z_2`, `Z_3`; the obstruction class in `H^2` is computable.
103. **Serre duality on the search variety.** Duality forces
     symmetry between "many solutions at small n" and "few
     solutions at large n"; translate into an explicit tradeoff.
104. **Open image theorem.** The image of the Galois action on the
     Tate module of the solution variety is open; use to force
     many Frobenius-eigenvalue combinations into the tuple.

### 34. Michael Atiyah

105. **Index theorem analogue.** Define a Dirac-type operator on
     the tuple whose index equals the signed number of Turyn
     orbits. Compute the topological side; compare with analytic
     side.
106. **K-theory of the configuration.** Turyn tuples define a
     vector bundle over the lag-torus; its K-theory class obstructs
     non-existence.

### 35. Richard Feynman

107. **Path integral.** Sum over all `(X, Y, Z, W)` with weight
     `exp(-β · Σ_s (N_X + N_Y + 2N_Z + 2N_W)²)`. Compute the `β →
     ∞` limit via steepest descent; saddle points are Turyn
     tuples. Use Monte Carlo Metropolis to sample — this *is* the
     `--stochastic` mode, and Feynman would push temperature
     schedules harder.
108. **Feynman diagram expansion.** Perturbatively expand in the
     interaction `(N_X + …)²`; pairings of positions = diagram
     edges. Connected diagrams count contributions to the Turyn
     partition function.
109. **Physics intuition: nearest-neighbour coupling.** Turyn
     tuples are the ground states of a 1-D Ising chain with
     carefully tuned long-range couplings. Use transfer-matrix
     methods: a `2^{4}` × `2^{4}` transfer matrix per position?

### 36. Paul Dirac

110. **Dirac-style factorisation.** Factor `(6n − 2)` into a
     product of linear operators on the ring `Z[C_n]`. If a
     factorisation exists, X, Y, Z, W can be read off its kernel.
111. **Delta-function identity.** Write `N_X(s) = δ_{s, 0} · n +
     …`; the Turyn identity as a delta distribution over `s`.
     Multiply by test functions (e.g. characters) to derive new
     constraints.
112. **Spinor representation.** Represent each pair `(x_i, y_i)` as
     a Pauli spinor; the XY coupling is a Pauli product. The Turyn
     constraint is a spin-spin invariant.

### 37. Claude Shannon

113. **Radar autocorrelation framing.** ±1 sequences with low
     autocorrelation sidelobes are literally CAZAC / Barker
     sequences used in radar. Mine the radar-code catalogue for
     long sequences with sidelobe 0 at some lags; assemble to form
     `(X, Y, Z, W)`.
114. **Information-theoretic bound.** Turyn tuples are codewords of
     a code with `H(codeword)` near the hypercube entropy minus
     the constraint entropy. Compute the entropy defect; it gives
     a lower bound on search effort.
115. **Noisy-channel decoding as SAT analog.** Turbo-code-style
     belief propagation on the factor graph of autocorrelation
     constraints.

### 38. Norbert Wiener

116. **Wiener–Khinchin identity.** Already central; its cousin,
     the Wiener deconvolution, estimates the missing middle of a
     sequence given boundary samples. Use Wiener filtering to
     *predict* best W middles from Z boundary, bypassing SolveW
     entirely.
117. **Wiener measure on sequence space.** Treat `±1^n` as a
     discretised Brownian path; Wiener expectation of
     autocorrelation squared has a closed form — use it as an
     Erdős-style second moment.

### 39. Maryam Mirzakhani

118. **Moduli space volume.** Treat the parameter space of
     continuous "Turyn-like" tuples as a symplectic moduli space;
     compute its Weil–Petersson volume. Integer points with volume
     > 0 per unit cell ⇒ many solutions.
119. **Geodesic counting.** Count closed geodesics on the moduli
     space; each geodesic corresponds to a family of near-Turyn
     tuples. Use asymptotic counting to predict solution density.

### 40. Peter Scholze

120. **Perfectoid reduction.** Work in the perfectoid tilt over
     `F_p`. The Turyn identity becomes a ±1 identity on an
     infinite-dimensional Witt vector; integer lifts are solutions.
     (Speculative but structurally interesting.)
121. **Prismatic cohomology.** Compute `H^*_prism(Turyn-scheme)`
     and use it to obstruct `n = 56`.

### 41. Donald Knuth

> "Beware of bugs in the above proof; I have only verified it, not tried it."

122. **Dancing Links (DLX) on the constraint hypergraph.** The
     autocorrelation relation is *exactly* an exact-cover-like
     structure on agreement/disagreement positions. Encode as DLX
     and apply Algorithm X. Faster than SAT for structured
     constraints.
123. **Knuth–Bendix completion.** Complete the rewriting system
     generated by BDKR rules (i)–(vi). The confluent rewriter
     normalises any candidate to canonical form in linear time.
124. **Literate benchmarking.** Measure, don't guess. Knuth would
     sub out all SAT calls for a pure instrumentation pass and
     build a histogram of where wall-clock actually goes. The
     answer may surprise us.
125. **TAOCP volume 4B approach.** Enumerate using Knuth's Gray
     code or revolving-door combination generator over boundary
     positions; reuse state between adjacent enumerations.

## Part IV — The home team: Hadamard and friends

> *Turyn, at the coffee urn:* "You're all welcome to help. But let me tell
> you what I *actually* know — and what I wish I'd known in '74."

### 42. Jacques Hadamard

126. **Hadamard inequality certificate.** If a TT(n) existed, the
     resulting Hadamard matrix `H` of order `4(3n-1)` satisfies
     `|det H| = (4(3n-1))^{2(3n-1)}`. Equivalently, the Gram
     matrix `H H^T = (4(3n-1)) I`. Use this to *verify* candidate
     matrices in O(n²) time without re-checking autocorrelation.
127. **Hadamard product (Schur) decomposition.** The autocorrelation
     matrix `A_X = X X^T` (circulant form) satisfies
     `A_X + A_Y + 2A_Z + 2A_W = (6n − 2) I`. This is a Hadamard /
     Schur-product identity — diagonalise in the Fourier basis and
     each diagonal entry is a scalar constraint. (Same as
     spectral, but the matrix form suggests a *block-diagonal
     branch-and-cut* structure.)
128. **Three factor-types (−1, 0, +1) Hadamard matrices.** Try
     constructions using balanced ternary matrices; there are more
     of them and they project onto Turyn tuples.

### 43. James Joseph Sylvester

129. **Sylvester construction.** Recursive doubling:
     `H_{2n} = [[H_n, H_n], [H_n, -H_n]]`. Look for Turyn tuples
     whose induced Hadamard matrix has Sylvester sub-blocks — this
     forces palindromic structure we can pre-enforce.
130. **Law of inertia.** The signature of the quadratic form defined
     by the autocorrelation matrix must be compatible with
     ±-coordinates. Mismatched signatures = infeasibility
     certificates.
131. **Sylvester's four-point covering problem.** Obscure but
     beautiful: the combinatorics of 4-subsets of positions relates
     to our 4-sequence structure.

### 44. Raymond Paley

132. **Paley construction.** Quadratic residues `χ_p(i)` modulo a
     prime `p ≡ 3 (mod 4)` give a ±1 sequence with controlled
     autocorrelation (all `N(s) = −1`). For `n` such that a useful
     `p` exists, *seed* Z or W with `χ_p` and search only X, Y, and
     a middle perturbation.
133. **Paley-type biquadratic residues.** For `p ≡ 1 (mod 4)`,
     quartic residues give ternary sequences; project to ±1 and
     use.
134. **Paley–Turán bound.** Combined bound on the character sum
     gives explicit tightening of Turyn's spectral-flat
     requirement.

### 45. John Williamson

135. **Williamson's four-matrix theorem.** If `(A, B, C, D)` are
     `n × n` symmetric circulant ±1 matrices with `A² + B² + C² +
     D² = 4n I`, then `[[A, B, C, D], [-B, A, -D, C], [-C, D, A,
     -B], [-D, -C, B, A]]` is Hadamard of order `4n`. This is
     *isomorphic* to the Turyn identity at certain `n`; port
     Williamson-search machinery (quaternionic representations)
     directly.
136. **Quaternionic viewpoint.** Bundle the 4 sequences as a single
     quaternion-valued sequence `Q = X + Y·i + Z·j + W'·k` (with
     appropriate length-matching for W). The Turyn identity is a
     "quaternionic norm is constant" condition. Exploit
     quaternion arithmetic and its subgroups.
137. **Paley–Williamson–Turyn families.** Kotsireas and others
     catalogued sub-families where one of `X, Y, Z, W` is
     palindromic or anti-palindromic. Enumerate by sub-family and
     pick the most constrained first.

### 46. Richard J. Turyn

138. **Base sequences first.** Turyn-type sequences reduce to base
     sequences `(a; b)` of length `n + (n-1) = 2n - 1` satisfying a
     single autocorrelation identity. Any `TT(n)` yields base
     sequences at `n = 2n − 1`. Invert: use known base sequences
     at odd lengths to *seed* Turyn candidates.
139. **T-sequences as intermediate targets.** Turyn→T→Hadamard; the
     T-sequence level has a much smaller search (4 sequences of
     length `2n-1`, fewer constraints). If T-sequences exist at
     some odd `m`, work backwards to Turyn `n = (m+1)/2`.
140. **Original Turyn trick.** Turyn exploited near-symmetries:
     reverse + negate. Those are T1, T2, T3. But Turyn's manual
     searches also used `(X + Y)` and `(X − Y)` as 0, ±2
     sequences; the support patterns of these must be
     complementary. Encode as a support-complement constraint.
141. **Turyn's 1974 unused observation.** Best, Djokovic et al.
     note that Turyn's original paper hints at a "pairing
     property" of (Z, W). The pairing reduces the Z × W search to
     a single combined sequence with fewer degrees of freedom;
     re-read and formalise.

### 47. Best, Đoković, Kharaghani, Ramp (BDKR)

142. **Full canonical form, fully enforced at every level.** The
     code implements (i)–(vi) across multiple layers but still has
     tuple-level dedup that costs ~9× slowdown. Push rule
     enforcement *earlier*: at MDD generation time, structurally
     prune the ZW layer by rule (iv)/(v) boundary checks and
     avoid runtime pre-filters.
143. **Equivalence class enumeration.** BDKR showed orbit count
     grows like `~f(n) / 1024`. For open `n`, compute the *expected*
     orbit count from combinatorial density; if < 1 on average, a
     solution's existence is a delicate matter and probably
     requires extra structure (e.g. palindromic Z).
144. **Djoković–Kotsireas sub-family for n ≡ 0 (mod 2).** The 2025
     solutions at n=40, 42, 44 use specific sub-families; extend
     those sub-families to n=46, 48, …, 56 and search only there.
145. **Power-of-two n.** n=32 is open and is `2^5`. There may be a
     special family using Walsh–Hadamard structure; search X, Y
     inside the Walsh basis.

### 48. Atle Selberg

146. **Selberg sieve on sum-tuples.** Sieve the sum-tuple set by
     congruence conditions; Selberg's upper-bound sieve may
     dramatically cut tuple count for certain n.
147. **Trace formula.** Apply Selberg trace formula on the
     automorphic side of the generating function; the spectral
     side gives counts.

### 49. André Weil

148. **Weil character-sum bound.** `|Σ χ(a_i) e(θ i)| ≤ (something)
     √n`. Encode directly as a per-frequency bound in the SAT
     solver. Tighter than current `|X(ω)|² ≤ 6n − 2`.
149. **Riemann hypothesis over F_p.** Already used implicitly via
     Paley; make it explicit in the X-Y SAT solver. Any
     `X = (polynomial evaluation mod p)` with small Weil bound.
150. **Adelic viewpoint.** The Turyn identity at a prime `p`
     interacts with the identity at `∞`; enforce Hasse's local-
     global principle across finitely many primes.

### 50. Pafnuty Chebyshev

151. **Chebyshev polynomial basis.** Expand each sequence in the
     Chebyshev polynomial basis; the orthogonality of `T_k` on
     `[-1, 1]` gives a diagonal form for certain autocorrelation
     sub-sums.
152. **Chebyshev inequality on moments.** Use Chebyshev-Markov
     moment inequalities to bound the number of "spiky"
     frequencies for X, Y, Z, W; tighten spectral bound at
     moderate θ.
153. **Chebyshev distance in local search.** Use `L^∞` norm of
     autocorrelation violation as the stochastic-search loss,
     rather than `L^2`. Shifts the landscape and may escape local
     minima the current `--stochastic` gets stuck in.

## Part V — Hallway conversations (cross-pollination)

> The coffee urn empties. Mathematicians pair off. The most productive
> conversations turn out not to be the plenary talks.

### Fourier × Wiener × Tao

154. **Fourth-moment concentration.** Combine Tao's
     `Σ|X̂|⁴ ≤ (6n-2) max|X̂|²` with Parseval `Σ|X̂|² = n` and
     Wiener–Khinchin on Turyn. Gives a *lower* bound on the
     *flatness* of each of X, Y, Z, W individually:
     `max_ω |X(ω)|² ≥ n / (1 + ε(n))`. That excludes any sequence
     whose spectrum is sharply concentrated. SAT-encode by
     forbidding low-spread spectra.

### Fermat × Gödel

155. **Descent as Gödel-proof witness.** Encode infinite descent in
     Lean: if TT(n_0) exists, a descent chain terminates by
     well-founding of BDKR weight. Failed descents (bounded
     searches) yield machine-checked infeasibility certificates
     for open small n.

### Euler × Ramanujan × Deligne

156. **Theta series of sum-tuples.** The number of integer
     `(σ_X, σ_Y, σ_Z, σ_W)` satisfying the sum-squared identity is
     the coefficient of `q^{6n-2}` in a specific theta product.
     Closed-form via Ramanujan identity; at the Galois level
     Deligne's bounds give it an `O(σ_0(6n-2))` bound. Use for a
     tight Phase A count prediction — *replace* the existing
     enumerator with a theta-generating-function counter + random
     sampler.

### Erdős × Kolmogorov

157. **Compressible-sequence LLL.** Restrict to sequences with
     Kolmogorov complexity ≤ K = c·log n. LLL hypotheses are
     easier to check on this small subset. A positive-probability
     argument on compressible sequences either finds a solution or
     forces incompressibility.

### Conway × Coxeter × Galois

158. **Reflection-group orbit game.** Play a game on the BDKR
     orbit: each move applies a generator. Win condition: reach
     canonical rep. Game length (surreal temperature) measures how
     hard the canonicalisation is and which rules are worth
     enforcing more aggressively. The code already does rule
     (iv)/(v) boundary pre-filter; (ii)/(iii)/(vi) MDD pre-filters
     may not yet be as tight as they could be.

### Williamson × Hadamard × Turyn

159. **Plug the 4 Williamson matrices into Turyn.** Each Williamson
     matrix is a circulant ±1 matrix. Its first row is a candidate
     *pre-sequence* for X, Y, Z, or W. Cross-index the Williamson
     database by `(n, row-structure)`; hand to the SAT solver as
     hard assumptions.

### Newton × Lagrange × Feynman

160. **Simulated annealing on the Lagrangian.** Replace the current
     simulated-annealing loss `Σ (N_X + N_Y + 2N_Z + 2N_W)²` with
     the augmented Lagrangian
     `L(x, λ) = Σ_s λ_s (N_X + …) + ρ/2 Σ (N_X + …)²`. Alternate
     between gradient steps on `x` and dual updates on `λ`; use
     Newton's method for the `x`-step. Accelerates the local
     search and may reach n=20+ stochastically (currently capped
     at ~18).

### Shannon × von Neumann × Wiener

161. **Information-theoretic priority for MDD walk.** Replace LCG
     permutation with an entropy-guided walk: pick the next path
     that *maximises expected information gain* about
     "SAT/UNSAT" for downstream XY solves. A simple proxy: lag-
     entropy of the boundary. This directly attacks the toc-ideas
     constraint ("quality of (Z,W,boundary) reaching XY").

### Gauss × Paley × Selberg

162. **Sieve through the Legendre-symbol hyperplane.** Sieve the X
     search by the Legendre symbol of a shift, using Selberg's
     sieve in place of simple enumeration. For `p ≈ n`, forbid X
     whose character sum with `(·|p)` falls outside a narrow band.

### Feynman × Kolmogorov × Turing

163. **Learned Metropolis proposals.** Train a small neural net on
     the state-dependent flip distribution from `--wz=sync`
     telemetry. Replace uniform proposals with learned proposals.
     Feynman would accept it — amplitudes summed, just with
     biased distributions.

### Atiyah × Grothendieck × Tao

164. **Motivic zeta of Turyn.** Define the motivic zeta function of
     the Turyn scheme; compute its leading coefficient at the
     special point. Its value distinguishes "exists" from "does
     not exist" for open n.

### Lagrange × Hilbert × Williamson

165. **SOS + four-squares hybrid.** The constraint `σ_X² + σ_Y² +
     2σ_Z² + 2σ_W² = 6n − 2` is a four-square form (Lagrange's
     theorem). Each autocorrelation identity is a quadratic
     polynomial. Combine: SOS certificate with four-square
     coefficient structure — a *structured* Positivstellensatz
     that is cheaper to solve than the general case.

### Mirzakhani × Poincaré × Ramanujan

166. **Topology × modularity of the orbit space.** The moduli space
     of Turyn tuples modulo BDKR is a `(4n-1) − 1024`-covered
     orbifold. Its Euler characteristic is a Ramanujan-like
     modular form in n. Compute χ(n) for `n ≤ 44`; extrapolate to
     56 and check against empirical orbit counts.

### Cantor × Wiles × Serre

167. **Diagonalised Galois representation.** Associate to each
     partial Turyn tuple a Galois rep; diagonalise over the Hecke
     algebra. Each eigencomponent is one constraint block; solve
     block-by-block.

## Part VI — Ideas from fresh blackboards (50 more)

A second wave of ideas bubbled up while the first wave was written.
These are tagged with the mathematician who sparked them, even when
they were voiced by someone else.

168. **Tensor-network contraction (Penrose).** Express the
     autocorrelation identity as a tensor network; contract it via
     tropical / min-plus arithmetic for a lower bound on
     infeasibility.
169. **Lovász theta function.** Encode the XY-extension graph;
     bound its independence number by `ϑ(G)` to rule out tuples
     that can never be extended.
170. **Brouwer fixed-point construction.** Define a continuous map
     on `[−1, 1]^{4n−1}` whose fixed points are exactly ±1 Turyn
     tuples. Brouwer guarantees at least one fixed point per
     contractible fiber. Approximate via Banach iteration.
171. **Banach contraction on autocorrelation.** Iterate `x ←
     sign(x − η · ∇loss)` with adaptive step; the contraction
     mapping principle gives convergence under curvature bounds.
172. **Dyson–Mehta random-matrix spacing.** The gaps between
     eigenvalues of the autocorrelation circulant obey a universal
     law for random ±1; Turyn tuples violate it in a specific
     way. Detect and prune.
173. **Selberg integral identity.** Express the Turyn generating
     function as a Selberg-type integral; asymptotic for integer
     points.
174. **Modular-form coefficient test.** Compute the 56-th Fourier
     coefficient of a well-chosen weight-`k` form and compare to
     the predicted Turyn count.
175. **Drinfeld associator.** Probably overkill, but the four
     sequences fit a 4-braid representation; the associator gives
     a natural action on tuples.
176. **Langlands-style reciprocity.** Match automorphic
     representations to Galois reps; Turyn tuples correspond to
     specific automorphic forms over `GL_4`. Long shot but big
     payoff.
177. **L-function with a twisted Turyn character.** Define
     `L(s, χ_Turyn) = Σ N(a; X,Y,Z,W) / a^s`; the location of its
     zeros predicts distribution of valid tuples.
178. **Gröbner basis with POT/TOP ordering.** The ideal
     `(x_i² − 1, autocorr_s)` in `Q[x_1..x_{4n-1}]` has a Gröbner
     basis that *fully solves* the problem. Infeasible for n=56,
     but for n ≤ 20 it finishes and yields hints.
179. **F4/F5 algorithm (Faugère).** Compute the Gröbner basis
     faster via matrix reduction. Combined with symbolic
     preprocessing of autocorrelation identities, n ≤ 24 might
     finish.
180. **Cylindrical algebraic decomposition.** Decompose the real
     variety into sign-invariant cells; each cell either contains
     Turyn tuples or doesn't.
181. **Sum-of-squares hierarchy (Lasserre).** Level-2 SOS
     relaxation gives a semidefinite program whose feasibility
     implies existence of a Turyn tuple at `n`. Infeasibility
     implies none at that level.
182. **Gram-matrix sampling.** Draw random positive-semidefinite
     matrices `G` with `diag(G) = 1` and spectrum concentrated,
     then pluck ±1 tuples from the closest-vertex rounding.
183. **Nullstellensatz certificate.** If Turyn(n) = ∅, Hilbert's
     Nullstellensatz gives polynomials `(p_i)` with `Σ p_i · f_i =
     1` where `f_i` are the defining constraints. Search for such
     certificates at bounded degree (~3-4).
184. **Goethals–Seidel array pre-search.** The Goethals–Seidel
     array converts `(X, Y, Z, W)` into a Hadamard matrix. Search
     among known 428-order Hadamard matrices (Kharaghani 2005)
     for Goethals–Seidel-like decompositions that hint at the
     Turyn tuples used.
185. **Turán-type number theory.** Turán's theorem on trigonometric
     polynomials gives oscillation bounds for sequences with
     bounded support; apply it to the partial autocorrelation
     function.
186. **Tate's thesis analogue.** Local–global analysis of Turyn
     identity at each place; Tate's thesis gives functional
     equations that may constrain the generating function.
187. **p-adic interpolation (Kubota–Leopoldt).** p-adic L-functions
     interpolate character sums; use them to lift F_p partial
     solutions to Z.
188. **Iwasawa theory.** Study the family of Turyn schemes as n
     varies with a fixed 2-adic structure.
189. **CFT (class field theory) for cyclotomic Z.** If Z is from a
     cyclotomic construction, CFT determines its autocorrelation
     class and narrows X, Y, W choices.
190. **Local Langlands for GL_2.** The autocorrelation of X+Y
     sequences factors through `GL_2(Z/nZ)` representations;
     classify by local Langlands.
191. **Zassenhaus–Scholz subgroup enumeration.** Enumerate subgroups
     of the BDKR T-group to find stabiliser-orbits; match to
     expected palindromic Turyn tuples.
192. **Brauer group obstruction.** Compute Brauer class of the
     Turyn variety; non-trivial Brauer class rules out solutions
     at that n.
193. **Heuristic arithmetic geometry.** Apply Batyrev–Manin-style
     conjectures on point counts of the Turyn variety; the
     expected count at n=56 is a specific positive rational — if
     < 1, don't even try.
194. **Entropy-compression argument (Moser).** Moser's
     entropy-compression proof of LLL gives a constructive
     algorithm for random sampling + local fix. Adapt to Turyn
     autocorrelation constraints.
195. **Derandomisation via conditional probabilities.** Convert
     LLL-style probabilistic existence into a deterministic
     algorithm using pessimistic estimators on
     `Σ_s (N_X + …)²`.
196. **Min-entropy hardness / lower bound.** Prove that any
     algorithm requires Ω(exp(n^c)) time to find TT(n), giving a
     negative result that refocuses effort. Or: prove it's in P
     (unlikely) via algebraic reduction.
197. **Tropical semiring relaxation.** Replace `+, ×` with
     `max, +`; the tropical Turyn identity is a piecewise-linear
     condition. Solutions of the tropical version are a skeleton
     of the real solutions.
198. **Matroid theoretic basis-swap.** The 4-set matroid on
     sequence positions admits basis-swap moves; use them to
     generate local neighbours in simulated annealing with
     provably connected state-graph.
199. **Frobenius reciprocity.** Induce characters from the BDKR
     subgroup to the full symmetry group; decompose the indicator
     of Turyn tuples into irreps; largest irrep components get
     priority in search.
200. **Persistent homology of the search tree.** Compute the
     0-dimensional persistence diagram of XY-SAT/UNSAT outcomes
     across MDD paths; long-lived components are "promising
     regions" — bias the LCG walker to revisit them.

## Part VII — Whiteboard synthesis (what's actually worth trying)

> Tao, Knuth, and Turyn converge at the whiteboard. Everyone else is in
> the hallway arguing. The three of them silently circle the ideas that
> would actually move the TTC needle this month.

### A. Cheap experiments (1–10 engineer-hours each)

The following are all small enough to try and measurable against
current TTC. Each is tagged with its idea number(s).

- **[#15, 45, 50, 132, 144] Paley/cyclotomic Z families.** Pre-build a
  table of Paley, Rudin-Shapiro, Legendre, and Walsh ±1 sequences of
  length n. For each, check that its autocorrelation sum fits the
  sum-tuple constraint. Run `--test-zw` with Z = one of these,
  brute-forcing W. This is literally `target/release/turyn
  --test-zw=<seqs>` and costs <1s to set up per n. If TT(28) falls out
  of this in a weekend, we're done.
- **[#64, 94, 148] Tighter per-frequency Weil-style spectral bound.**
  Replace `|X(ω)|² ≤ 6n − 2` with the sharper `|X(ω)|² ≤ n + 2√n ·
  (bound_from_weil)`. One-line change in `SpectralConstraint`; test
  at n=26.
- **[#116, 161] Entropy-guided MDD walk replacing LCG.** The Monitor
  thread currently uses LCG-scrambled path indices. Replace with a
  greedy "maximum spectral-flat first" ordering: compute cheap boundary
  flatness score, push high-score boundaries first. Hypothesis: cuts
  XY-UNSAT fraction by 2×.
- **[#78, 100] Increase θ in SpectralConstraint.** Currently θ is
  chosen around the FFT size; push θ to the next power of 2 after
  `8n`. Measure effect on `flow_z_spec_pass` per unit time.
- **[#122, 125] DLX on the boundary cover.** Re-encode the XY SAT as
  Knuth's DLX exact cover — it matches the "pick n-1 lag positions to
  agree" structure natively. Likely big speedup at small n; unclear
  at n ≥ 22.
- **[#140, 141] (X + Y)/2, (X − Y)/2 reformulation.** Search in the
  variables `u = (X + Y)/2 ∈ {−1, 0, 1}^n` and `v = (X − Y)/2 ∈
  {−1, 0, 1}^n` with support complementarity `|u_i| + |v_i| = 1`.
  Encode this directly — cuts a factor 2 from the XY variable count
  at the cost of adding a ternary constraint. Worth measuring
  carefully.
- **[#52, 194, 195] Moser-style constructive LLL.** Write a simple
  Moser–Tardos procedure: random ±1 tuple, resample any
  autocorrelation constraint that is violated, repeat. For small n,
  check whether it hits a Turyn in reasonable time. If LLL hypothesis
  is close to tight, Moser will work.
- **[#56] Low-K-complexity seed pool.** Enumerate all LFSR-generated
  sequences of length n with register size ≤ 10, and feed them as Z
  candidates via `--test-zw`. Known TT(40,42,44) are short enough to
  describe; check whether open `n` sequences have similar low-K
  structure.
- **[#126] Hadamard Gram-matrix spot-check.** Before committing to
  SAT on XY, verify that a rank-deficient Gram matrix can't rule out
  the boundary. Cheap pre-filter.
- **[#60, 70, 198] Local-search neighbourhood via BDKR generators.**
  Currently simulated annealing uses single-bit flips. Replace with
  BDKR orbit generators (reverse, alternate, swap) + single-bit flip.
  Larger neighbourhood = better escape.

### B. Medium experiments (1–10 engineer-days each)

- **[#107, 160] Augmented Lagrangian stochastic search.** Replace
  `--stochastic` loss with augmented Lagrangian; alternate primal /
  dual updates. Plausibly reaches n=24+ stochastically.
- **[#135, 136] Williamson-seeded quaternionic search.** Search in
  quaternion basis; enforce `|Q(ω)|² = const`. Port Williamson
  search code if available.
- **[#128, 184] Ternary Hadamard decomposition.** Search balanced
  ternary matrices of order 4(3n-1) whose Goethals–Seidel
  decomposition factors through a Turyn tuple.
- **[#168] Tensor-network contraction for infeasibility.** Build the
  tensor network; contract it tropically; a zero-valued contraction
  proves infeasibility.
- **[#122, 178] DLX and Gröbner hybrid.** At small n, compute a
  reduced Gröbner basis of the autocorrelation ideal; cache reductions
  and use them as implied clauses in SAT.
- **[#39, 163] ML-guided priority queue.** Train a GBT on
  `(boundary features, tuple) → XY-SAT outcome`. Prioritise queue by
  predicted SAT probability. The telemetry from `--wz=sync` already
  has the right features.

### C. Ambitious / long-horizon

- **[#155] Mechanised descent proof of TT(n) non-existence in Lean.**
  Would provide a publication-quality infeasibility proof at any
  open n that turns out empty.
- **[#181] Level-4 Lasserre SOS SDP.** The SDP size is
  `O(n^8)` — feasible up to n ≈ 20 with hybrid solvers. At such n
  solutions are known, so the check is: does SOS *prove* they exist?
  Then scale up.
- **[#142] Refactor: BDKR rules enforced structurally in MDD gen.**
  Cheapest asymptotic win available — and partially done; finishing
  rule (ii)(iii)(vi) boundary pre-filters inside MDD-gen could give
  ~5× orbit reduction at large k.

### D. Breakthrough candidates (if we want to bet)

The four mathematicians who were most animated at the end of the
symposium singled out one idea each:

1. **Ramanujan — idea #31/174.** The count of Turyn tuples is very
   likely a Fourier coefficient of a modular form; compute the first
   20 coefficients explicitly, fit a form, predict TT(56) count.
2. **Turyn — idea #141.** "There is a pairing in (Z, W) I never
   wrote up. Someone please read my 1974 preprint carefully."
3. **Tao — idea #154.** "The fourth-moment bound plus the spectral
   identity forces `max|X̂|² ≥ n`. That alone rules out many Z
   and W with existing `SpectralConstraint` logic — tighten it."
4. **Erdős — idea #52.** "LLL must work. If not constructive,
   at least nonconstructive — prove a Turyn tuple exists at n=56,
   then we search with renewed hope."

## Part VII.5 — Experimental log (the morning after)

Some of the ideas actually got tried. Results in execution order.

### #154 Tao fourth-moment / Parseval floor — no new pruning

Checked on every known `TT(n)` for `n ≤ 44`. The Turyn identity plus
Parseval gives trivially `avg_ω |X̂(ω)|² = n`, hence
`max_ω |X̂(ω)|² ≥ n` as a free consequence of the identity. All known
solutions satisfy this and their actual `max|X̂|²` values range from
`n` to roughly `10n`. No single-sequence lower bound that's useful
as a SAT constraint beyond what is already enforced pointwise by
`SpectralConstraint`. **Verdict: measured but not actionable.**

### #52 / #194 Moser-style constructive LLL — does not scale

Python reference implementation: random `±1^{4n-1}`, pick a violated
lag, resample all bits that touch it, repeat.

| n | time to find | steps   |
|---|--------------|---------|
| 4 | instant      | 352     |
| 6 | instant      | 2,877   |
| 8 | instant      | 23,248  |
| 10 | did not find in 10s | >218k |
| 12 | did not find in 10s | >174k |

Scaling looks exponential. The existing `--stochastic` simulated
annealing already solves to `n = 18`, so Moser is strictly weaker.
**Verdict: implemented, dominated.**

### #140 `N_Z + N_W ∈ [-(n-s), n-s]` — already implemented

Derivation: `x_i x_{i+s} + y_i y_{i+s} = 2 x_i x_{i+s}` when
`a_i a_{i+s} = +1` (where `a_i = x_i y_i`), else `0`. So
`N_X(s) + N_Y(s) = 2 · Σ_{i ∈ S_s} x_i x_{i+s}` with
`|S_s| ≤ n − s`, giving `|N_Z(s) + N_W(s)| ≤ n − s`.

This is *exactly* the bound at `src/mdd_pipeline.rs:1204–1230`
(`max_nzw = (n - s) as i32`). The idea was rediscovered; the code
already enforces it. **Verdict: already present.**

### #140b Novel saturation observation — *all* known TT(n) hit `|N_Z+N_W| = |S_s|` somewhere

For every known solution `TT(n)`, `n ∈ {4, 6, …, 44}`, there exists
at least one lag `s` with

    |N_Z(s) + N_W(s)| / |S_s| = 1.0

where `S_s = {i : a_i a_{i+s} = +1}`. That is, *the agreement set
must be 100% uniform-signed at that lag*. This is not currently used
as a pruning heuristic, and it's a free pre-filter:

- Given a candidate `(Z, W)` boundary, compute `c_s = |N_Z(s) + N_W(s)|`.
- A solution requires `c_s ≤ n − s` at every lag (already enforced).
- But additionally, for *some* lag, a solution requires `|S_s| = c_s`
  **exactly**, which forces a hard unification among the `x_i x_{i+s}`
  on agreement positions.

Implementation suggestion: prioritise XY solves whose `(Z, W)`
has at least one lag with `c_s` *close to* `n − s`. These boundaries
have the tightest unification constraints and are most likely to
either SAT quickly or UNSAT quickly. Add to the gold-queue scoring
function. **Verdict: candidate heuristic; not yet implemented.**

### Baseline n = 28 (180 s, `--wz=apart --mdd-k=9`)

- 264 575 boundaries walked (0.13 % of 211 M live ZW paths)
- 21.6 M Z solutions, **100.0 %** Z pair-spectral fail
- 326 reach XY stage, 162 019 XY SAT solves, **100.0 %** UNSAT
- **TTC ≈ 1.7 days** at 16 threads.

Interpretation: the spectral pair filter is brutal (good). All 326
XY-reaching boundaries failed UNSAT. That's evidence either TT(28)
doesn't exist in the canonical form, or its boundary is not among
these 0.13 %. A full ~41-hour overnight run would settle
**existence** at mdd-k=9 with current pipeline.

### #132 Paley/Legendre Z seeds — partial

For `n ∈ {28, 30, 32, 36, 38}`, computed `Z_i = (i | p_n)` for the
smallest prime `p_n > n`. Autocorrelation profiles are Paley-small
but *not* matching any known TT Z structure. The known Z sequences
at `n ≤ 44` do **not** exhibit Legendre structure (verified: their
profiles don't match the Paley family).

Full test would require `--test-zw=Z,W` for each candidate W. Enumerating
W at `n = 28` is 2^27 = 134 M, but restricted by `σ_W ∈ sum-tuple`
and rule (i) pinning, still ~2^22 candidates — borderline. This test
was **not executed**; set up for a follow-up pass.
**Verdict: preliminary only.**

## Part VIII — Closing remarks from the chairs

> *Gauss:* "Every simple problem deserves a Gauss sum."
>
> *Hilbert:* "Wir müssen wissen — wir werden wissen."
>
> *Noether:* "Find the hidden symmetry that makes `6n − 2` *obvious*,
> and the problem will dissolve."
>
> *Turyn:* "I wish I'd had a computer in '74. You have them now.
> Use them."
>
> *The session adjourns. The whiteboard is photographed.*

---

## Index of originators (for quick reference)

| # | Mathematician | Ideas |
|---|---|---|
| 1 | Fermat | 1–3 |
| 2 | Descartes | 4–6 |
| 3 | Newton | 7–9 |
| 4 | Euler | 10–13 |
| 5 | Gauss | 14–17 |
| 6 | Riemann | 18–20 |
| 7 | Hilbert | 21–24 |
| 8 | Poincaré | 25–27 |
| 9 | Noether | 28–30 |
| 10 | Ramanujan | 31–34 |
| 11 | Gödel | 35–37 |
| 12 | Turing | 38–40 |
| 13 | von Neumann | 41–44 |
| 14 | Galois | 45–47 |
| 15 | Abel | 48–49 |
| 16 | Cantor | 50–51 |
| 17 | Erdős | 52–55 |
| 18 | Kolmogorov | 56–59 |
| 19 | Conway | 60–63 |
| 20 | Tao | 64–67 |
| 21 | Coxeter | 68–70 |
| 22 | Grothendieck | 71–74 |
| 23 | Maxwell | 75–77 |
| 24 | Fourier | 78–80 |
| 25 | Laplace | 81–83 |
| 26 | Lagrange | 84–86 |
| 27 | Cauchy | 87–89 |
| 28 | Lebesgue | 90–91 |
| 29 | Hardy | 92–94 |
| 30 | Littlewood | 95–97 |
| 31 | Wiles | 98–99 |
| 32 | Deligne | 100–101 |
| 33 | Serre | 102–104 |
| 34 | Atiyah | 105–106 |
| 35 | Feynman | 107–109 |
| 36 | Dirac | 110–112 |
| 37 | Shannon | 113–115 |
| 38 | Wiener | 116–117 |
| 39 | Mirzakhani | 118–119 |
| 40 | Scholze | 120–121 |
| 41 | Knuth | 122–125 |
| 42 | Hadamard | 126–128 |
| 43 | Sylvester | 129–131 |
| 44 | Paley | 132–134 |
| 45 | Williamson | 135–137 |
| 46 | Turyn | 138–141 |
| 47 | BDKR | 142–145 |
| 48 | Selberg | 146–147 |
| 49 | Weil | 148–150 |
| 50 | Chebyshev | 151–153 |
| — | Hallway cross-pollination | 154–167 |
| — | Second-wave ideas | 168–200 |

