// #import "@preview/knowledge-key:1.0.1": *
#import "@preview/colorful-boxes:1.4.1": *


#let knowledge-key(
  title: [Paper Title],

  // An array of authors. For each author you can specify a name,
  // department, organization, location, and email. Everything but
  // but the name is optional.
  authors: (),

  // The article's paper size. Also affects the margins.
  paper-size: "a4",

  // The content.
  body
) = {
  let line_skip = 0.4em
  let font_size = 8pt
  let level1_color = "#264653";
  let level2_color = "#2A9D8F"; 
  let level3_color = "#00B4D8"; 
  let level4_color = "#6A4C93"; 
  let level5_color = "#8D99AE"; 

  show: set block(below: line_skip)
  show: set par(leading: line_skip, justify: false)
  
  // Configure the page.
  set page(
    paper: paper-size,
    flipped: true,
    margin: ("top": 6mm, "rest": 1mm),
    header-ascent: 1.5mm,
    header: align(center, text(
      1.1em,
      weight: "bold",
      [#title / #authors],
    )),
  )

  set text(size: font_size, font: "Noto Sans")

  set terms(hanging-indent: 0mm)

  show outline.entry.where(level: 1): set text(weight: "bold")

  show heading: set text(white, size: font_size)
  show heading: set block(
    radius: 0.65mm,
    inset: 0.65mm,
    width: 100%,
    above: line_skip,
    below: line_skip,
  )
  show heading.where(level: 1): set block(fill: rgb(level1_color))
  show heading.where(level: 2): set block(fill: rgb(level2_color))
  show heading.where(level: 3): set block(fill: rgb(level3_color))
  show heading.where(level: 4): set block(fill: rgb(level4_color))
  show heading.where(level: 5): set block(fill: rgb(level5_color))
  set heading(numbering: "1.1")

  columns(4, gutter: 2mm, body)
}

#show: knowledge-key.with(
  title: [Discrete Maths HS24],
  authors: "cs.shivi.io",
)

// #set text(font: "New Computer Modern")
// #show sym.emptyset: set text(font: "Fira Sans")
#show math.equation.where(block: true) : set align(left)
// #import "@preview/codelst:2.0.1": sourcecode

= Propositional Logic

== Basics

=== Basic Equivalences (Lemma 2.1)

1. *Idempotence:* $A and A equiv A$ and $A or A equiv A$
2. *Commutativity:* $A and B equiv B and A$ and $A or B equiv B or A$
3. *Associativity:* $(A and B) and C equiv A and (B and C)$ and $(A or B) or C equiv A or (B or C)$
4. *Absorption:* $A and (A or B) equiv A$ and $A or (A and B) equiv A$
5. *1st Distr. Law:* $A and (B or C) equiv (A and B) or (A and C)$
6. *2nd Distr. Law:* $A or (B and C) equiv (A or B) and (A or C)$
7. *Double Neg.:* $not not A equiv A$
8. *De Morgan:* $not (A and B) equiv not A or not B$ and $not (A or B) equiv not A and not B$

=== Logical Consequence

$F tack.r.double G$ is a *statement*. This statement is true if for all truth assignments $F => G$.

== Tautologies and Satisfiability

*Tautology:* A formula $F$ (denoted $top$ or $tack.r.double F$) is a "tautology" (or valid) or valid if it's underlying formula resolves to true for any and all interpretations.

*Satisfiable:* A formula $F$ is "satisfiable" if it's underlying formula can be made true for some arbitrary interpretation.

- *L2.2* $F$ is tautology iff $not F$ is unsat.
- *L2.3* $F->G$ is tautology iff $F tack.r.double G$.
    - $(arrow.r.double)$: Assume $F->G equiv top$. Then when $F$ is true $G$ MUST be true, hence $F tack.r.double G$
    - $(arrow.l.double)$: Assume $F tack.r.double G$. Then $F$ is true but $G$ is false can't exist, hence $F -> G equiv top$.

= Predicate Logic

*Definition:* A "$k$-ary" predicate $P$ on a universe $U$ is a function: $U^k -> {0,1}$.

== Quantifiers

- $forall P(x)$ means $P(x)$ is true for all $x in U$.
- $exists P(x)$ means $P(x)$ is true for at least one $x in U$.


_Example:_ $forall x ((P(x) and Q(x) -> (P(x) or Q(x))) equiv top$

== Useful Rules

#columns(2, [
- $... forall x forall y ... equiv ... forall y, forall x ...$
- $... exists x exists y ... equiv ... exists y, exists x ...$
- $forall x P(x) and forall x Q(x) equiv forall x (P(x) and Q(x))$
- $not forall x P(x) equiv exists x not P(x)$
#colbreak()
- $exists x (P(x) and Q(x)) tack.r.double exists x P(x) and exists x Q(x)$
- $not exists x P(x) equiv forall x not P(x)$
- $exists y forall x P(x,y) tack.r.double forall x exists y P(x,y)$
])

= Proof Patterns

== Proof of Implications

=== Composition of Implications

*L2.5:* $(A => B) and (B => C) tack.r.double A => C$

=== Direct Proof of an Implication

Assume $S$ and show $S => T$.

=== Indirect Proof of an Implication

Show the contrapositive implication, i.e. $not B => not A tack.r.double A => B$. (*L2.6*)

== Proof of Statements

=== Modus Ponens

Prove $S$ by: 1. Find and prove $R$ 2. Prove $R => S$

*L2.7:* $A and (A => B) tack.r.double B$

=== Case Distinction
Prove $S$ by: 1. Finding finite list of "cases" $A_1, A_2, ..., A_k$ 2. Showing at least one of the $A_i$ is true: $A_1 or A_2 or ... or A_k$ and 3. Showing $A_i => S "for" i = 1,...,k$. Note that for $k=1$ we are doing Modus Ponens...

*L2.8:* $(A_1 or ... or A_k) and (A_1 => B) and ... and (A_k => B) tack.r.double B$

=== Proofs by Contradiction
Prove $S$ by: 1. Find T and show $not T$ 2. Show that $not S => T$ (if $S$ were false we get a wrong/contradictory result).

*L2.9:* $(not A => B) and not B tack.r.double A$

== Existence Proofs

Effectively show that there exists an assignment of parameters from a parameter space $x in cal(X)$ such that the statement with that assignment becomes true, i.e $exists x in cal(X) (S_x)$.

*Constructive* proof provides a concrete example. *Non-Constructive* proof shows existence by proving otherwise.

=== Pigeonhole Principle

If a set of $n$ objects is partitioned into $k < n$ sets, the at least one of those sets contains $ceil(n/k)$ objects.

=== Proof by Conterexample

Obvious but... $exists x in cal(X) (not S_x)$.

== Proof by Induction

Meant to show $forall n P(n)$. Proof by 1. Prove basis step $P(0)$ then 2. Show $P(n) => P(n+1)$.

*Thm2.11*: $P(0) and forall n(P(n)->P(n+1)) => forall n P(n)$.

= Set Theory

A set is a new mathematical object which is defined by a single operation: the membership predicate ($x in S$ or $x in.not S$).

*Equality:* $A = B <=> forall x (x in A <-> x in B)$.

== Meta Operations

- $A subset.eq B <=> forall x (x in A -> x in B)$
- $A = B <=> (A subset.eq B) and (B subset.eq A)$
- $A subset.eq B and B subset.eq C => A subset.eq C$ (transitivity)
- $A union B = {x | x in A or x in B}$
- $A sect B = {x | x in A and x in B}$
- $B backslash A = {x in B | x in.not A}$

== Laws (Theorem 3.4)

- *Idempotence*, *Commutativity*, *Associativity*, *Absorption*, *Distribution*
- *Consistency:* $A subset.eq B <=> A sect B = A <=> A union B = B$

== Empty Set

$A = emptyset <=> forall x not (x in A)$

- *L3.5: Uniqueness of emptyset*
    - Let $emptyset$ and $emptyset'$ be arbitrary emptysets. Now show using definition of equality that $emptyset subset.eq emptyset'$ and vice versa (both are vacuously true)...
- *L3.6: Emptyset is subset of all sets*, i.e $forall A (emptyset subset.eq A)$.
    - By contradiction: $not(emptyset subset.eq A) <=> not forall x (x in emptyset -> x in A) <=> exists x not(not(x in emptyset) or x in A) <=> exists x (x in emptyset) and exists x not(x in A) => exists x (x in emptyset)$

== Meta Sets

- *Powerset:* $cal(P)(A) = {S | S subset.eq A}$
    - $|cal(P)(A)| = 2^(|A|)$
- *Cartesian product:* $A times B = {(a,b) | a in A and b in B}$
    - $|A times B| = |A| dot |B|$

= Relations

A (binary) relation is a subset of $A times B$: $rho subset.eq A times B$. $rho$ is called a relation "on A" is $A = B$. We often write $a rho b$ instead of $(a,b) in rho$.

*Identity Relation:* $mono(id)_A = {(a,a) | a in A}$.

*Possible relations:* There are $2^(n^2)$ relations on a set, since $n^2 = |A^2|$ and each of these pairs can be in/excluded.

*Inverse Relation:* $hat(rho) = {(b,a) | (a,b) in rho}$. Alternatively: $b hat(rho) a <=> a rho b$

*Composition of relations:* $rho circle.small sigma = {(a,c) | exists b ( a rho b and b sigma c)}$ 

== Types of Relations

- *Reflexive (D3.13):* $forall a in A (a rho a)$, i.e. $id subset.eq rho$. _Examples:_ $<=, >=, (| "on" ZZ backslash {0})$, _Non Examples:_ $<, >$
    - In a graph, we have self loops for all nodes.
    - *Irreflxive (D3.14):* $rho sect mono(id) = emptyset$
- *Symmetric (D3.15):* $a rho b <=> b rho a$ or $rho = hat(rho)$
    - *Antisymmetric (D3.16):* $a rho b and b rho a => a = b$ or $rho sect hat(rho) subset.eq id$. _Examples:_ $<=, >=, (| "on" NN "but not on" ZZ)$
        - In a graph: no cycle of length 2.
    - *L3.9:* $rho$ is transitive iff $rho^2 subset.eq rho$.
        - _"if ($arrow.l.double$):"_ Assume $rho^2 subset.eq rho$ i.e $a rho^2 b => a rho b$. If $a rho b and b rho c => a rho^2 c$ but by assumption $=> a rho c$ which exactly is transitivity.
        - _"only if ($arrow.r.double$):"_ Assume $rho$ is transitive. Then $a rho^2 b => exists c (a rho c and c rho b)$. By transitivity: $a rho b$. Hence $rho^2 subset.eq rho$.
    - *Transitive Closure (D3.18):* $rho^* = union.big_(n in NN backslash {0}) p^n$. i.e reachability with arbitrary finite steps.
        - $p^n subset.eq p$. Proof by induction:
            - Base Case: $p^1 subset.eq p$
            - Induction Step: $(a rho^(k+1) c => a rho^k b and b rho c =>  a rho b and b rho c "(By I.H)" => a rho c) => rho^(k+1) subset.eq rho$

=== Equivalence Relation

- *Equivalence Relationship (D3.19):* Relation that's 1) reflexive 2) symmetric and 3) transitive.
- *Equivalence Class (D3.20):* Let $theta$ be an equivalence relation on $A$. The equivalence class of $a$ is defined as: $[a]_theta = {b in A | a theta b}$. _Trivial Examples:_ $[a]_theta = A$ if $theta = A times A$, $[a]_theta = {a}$ if $theta = mono(id)$.
- *L3.10:* $theta = theta_1 sect theta_2$ and $theta$ is an equivalence relation. Trivial, since each pair in theta inherits reflexivity, symmetry and transitivity from $theta_(1 or 2)$.
- *Partition (D3.21):* Partition on a set $A$: ${S_i | i in cal(I)} ((S_i sect S_j = emptyset "for" i != j) and union.big_(i in cal(I)) S_i = A)$
- *Quotient Set (D3.22):* Set of equivalence classes denoted by: $A"/"theta = {[a]_theta | a in A}$. Also called $A mod theta$.
    - *Thm3.11:* $A"/"theta$ is a partition of $A$.

=== Posets

- *Partial Order Relation (D3.23):* Relation that's 1) reflexive 2) antisymmetric and 3) transitive. Denoted by $prec.eq$ i.e $(A, prec.eq)$ _Examples:_ $<=, >=$. _Non Examples:_ $<, >$ (since not reflexive)
    - $a prec b <=> a prec.eq b and a != b$
    - *D3.24: *$a,b$ are "comparable" if $a prec.eq b or b prec.eq a$, else "incomparable".
    - *Totally ordered (D3.25):* If any two elements are comparable then $A$ is totally ordered.

==== Hasse Diagrams

- *Cover (D3.26): *$a$ covers $b$ if $a prec b$ and $not(exists c (a prec c and c prec b))$.
- *Hasse Diagram (D3.27):* A digraph of a finite poset where $a->b$ iff $b$ covers $a$

==== Lexicographic Order

Let $(A; prec.eq), (B; subset.eq.sq)$. Now we define $(a_1, b_1) <= (a_2, b_2) <=> a_1 prec.eq a_2 and b_1 subset.eq.sq b_2$.

- *Thm3.12:* $(A; prec.eq) times (B; subset.eq.sq)$ is a poset.
- *Lexicographic Order (Thm 3.13):* $(a_1, b_1) <=_("lex") (a_2, b_2) <=> a_1 prec a_2 or (a_1 = a_2 and b_1 subset.eq.sq b_2)$ is also a poset.

==== Special Elements

Let $(A; prec.eq)$ be a poset and $S subset.eq A$, let $a in A$ then: (D3.29)
1. $a$ is minimal[maximal] of $A$ if $not(exists b in A (b prec a [b succ a]))$ 
   _tldr: no element of $A$ is strictly smaller/larger than $a$. Comparability with all elements is not required. There can be many minimal/maximal elements._
2. $a$ is least [greatest] element of $A$ if $forall b in A (a prec.eq b [a succ.eq b])$ 
   _tldr: comparable to all elements of $A$ and smallest/largest. The element is unique if it exists._
3. $a$ is lower [upper] element of $S$ if $forall b in S (a prec.eq b [a succ.eq b])$ 
   _tldr: comparable to all elements of $S$ and below/above them. There can be many or no lower/upper elements._
4. $a$ is greatest lower bound [least upper bound] of $S$ if $a$ is the greatest [least] element of the set of all lower [upper] bounds of $S$. 
   _tldr: the largest/smallest element that bounds $S$ from below/above._


*Well Ordered (D3.30):* A poset is well-ordered if it is totally ordered and every non-empty subset of $A$ has a least element.

==== Meet, Join, Lattices

- *Meet:* If the set ${a,b}$ has a glb, it's called the meet. Denoted by $a and b$.
- *Join:* If the set ${a,b}$ has lub, it's called the join. Denoted by $a or b$.
- *Lattice:* A poset where each pair of elements has a meet and lattice is called lattice.

= Functions

A function $f: A -> B$ from domain to codomain is a relation with properties:
1. Totally defined: $forall a in A exists b in B (b = f(a))$, i.e each element maps to atleast one element.
2. Well defined: $forall a in A forall b, b' in B (b = f(a) and b' = f(a) => b = b')$, i.e each element maps to maximally one element.

If only the 2nd condition holds, we call the function a partial function.

There are $|B|^(|A|)$ possible functions $A -> B$.

== Image/Preimage

- *Image/Range:* Let $f: A -> B, S subset.eq A$ then $f(S) = {f(a) | a in S}$. $Y = f(A), Y subset.eq B, Y = "Im"(f)$.
- *Preimage:* $T subset.eq T, f^(-1)(T) = {a in A | f(a) in T}$

== Function Types

- *Injective (1to1):* $a != b => f(a) != f(b)$, i.e unique mapping.
- *Surjective (onto):* $"Im"(f) = B$, i.e. each element in $B$ can be reached.
- *Bijective:* If both injective and surjective, i.e an invertible function defined for all elements of $B$.

= Un/Countability

1. $A tilde B$ if there exists a bijection $A -> B$
2. $A prec.eq B$ if 1) $A tilde C and C subset.eq B$ or 2) there exists an injection $A -> B$
3. If $A prec.eq NN$ then $A$ is countable. Otherwise uncountable.


*L3.15:*
1. $tilde$ is an equivalence relation
2. $prec.eq$ is transitive
3. $A subset.eq B => A prec.eq B$

*Thm 3.17:* $A$ is countable iff $A$ is finite or $A tilde NN$.

== Countable Sets

- *Finite bit sequences:* ${0,1}^* arrow.r.bar "decimal"("'1'"+"seq")$
- *Pairs of $NN$:* 1) $f: NN -> NN^2, f(n) = (k,m), k + m = t - 1 and m = n - binom(t, 2)$ or 2) $(a,b) arrow.r.bar 0^(|a|)|| 1 || a || b$
- *Rational numbers:* $QQ prec.eq ZZ times NN and ZZ tilde NN => QQ tilde NN$.

*Thm 3.22:*
1. $A$ countable $=> A^n$ countable.
2. $union.big_(i in NN) A_i$ is countable if $A_i$ is countable.
3. $A^*$ is countable if $A$ is countable.

== Uncountable Sets

- *Infinite bit sequences or set of functions $NN->{0,1}$:* By cantor's diagonalization...

== How to Approach

*Intuition:*
Understand what the set represents. Determine wether it's countable/uncountable. Let $A$ be the set which is uncountable.

*Proof (Uncountable):*
1. Find an injection: $f: {0,1}^oo -> A$ (we'll prove injectivity later)
2. Show $f$ is a function, i.e 1) each elements gets mapped to at least one element 2) each element gets mapped to maximally one element. 3) Do you actually map to $A$ and not somewhere else?
3. Proving injectivity: 1) $a, b in {0,1}^oo, a != b => ... => f(a) != f(b)$ or 2) $f(a) = f(b) => ... => a = b$
4. We have ${0,1}^oo prec.eq A$ but we need to add "for formality" that $A prec.eq.not NN$. We can argue this via transitivity since ${0,1}^oo prec.eq.not NN$.

*Tricks:*
- *Complement Trick:* To show $A$ is uncountable find $B$ also uncountable such that $A subset.eq B$. Now show that $B backslash A$ is countable. Sound since by contradiction if $A$ were countable, $A union (B backslash A) = B$ LHS would be countable but RHS isn't.
- *Prime Factorization:* e.g. $f: NN^2 -> N, f: (a,b) arrow.r.bar 2^a 3^b$. $f$ is injective since each number can be uniquely factored into primes by the FTA...


= Number Theory

- $a divides b$ if $exists c (a c = b)$. Every non-zero int divides $0$. $1, -1$ divide all integers.
- *Thm 4.1 (Euclid):* $forall a in ZZ and d != 0 exists q exists r (a = d q + r and 0 <= r < |d|)$

== GCD, LCM

*GCD (D4.2):* $gcd(a,b)=d$ if d divides both $a and b$ and is the greatest in terms of the divisibility relation.

*Relative Prime (D4.3):* Two numbers are rel. prime if $gcd(a,b)=1$.

- *L4.2:* $gcd(a, b - x a) = gcd(a,b)$. Proof by expanding into definition of $divides$ and showing $d_"LHS" = d_"RHS"$.
- $gcd(a, b) = gcd(m, R_m (n))$

*Ideal (D4.4):* $(a,b) = {u a + v b | u, a in ZZ}$

- *L4.3:* $exists d : (a, b) = (d)$.
    - _Show $(d) subset.eq (a,b)$:_ Trivially holds since d is smallest in $(a,b)$ then $(d) subset.eq (a,b)$
    - _Show $(a,b) subset.eq (d)$:_ Let $c in (a,b) => c = q d + r => r = c - q d$ but $0 <= r < d$ and $d$ is smallest in $(a,b) => r = 0 => c = q d => c in (d)$.
- *L4.4:* $(a,b)=(d) => d = gcd(a,b)$
    - $d in (a,b) <=> d = u a + v b$. Any common divisor $c$ of $a$ and $b$ must $divides d$. Since $a, b in (d)$ and transitivity of $divides => c | d$, $d$ is the gcd.

*LCM (D4.5):* $"lcm"(a,b) = l$ if both $a and b$ divide $l$ and it is the least in terms of the divisibility relation.

== Fundamental Theorem of Arithmetic (FTA)

*Prime (D4.6):* A positive integer $p > 1$ is prime if it's only positive divisors are $1 and p$. $not$ prime = composite.

*FTA (Thm 4.6):* TLDR: Every number can be uniquely factored intro a product of primes.

Alternate GCD and LCM definition:
- Let $a = product_i p_i^e^i$ and $b = product_i p_i^f^i$
- $gcd(a,b) = product_i p_i^min(e^i, f_i)$ and $"lcm"(a,b) = product_i p_i^max(e^i, f_i)$
- $=> gcd(a,b) dot "lcm"(a,b) = a b$

== Modular Arithmetic

$a equiv#sub[m] b <=> m | (a-b)$

*L4.14: Compatibility with Arithmetic Operations*

If $a equiv#sub[m] b and c equiv#sub[m] d$, then:
1. $a+c equiv#sub[m] b + d$
    - $m | (a - b) and m | (c - d) => m | ((a-b) + (c-d)) => m | ((a+c)-(b+d)) => a+c equiv#sub[m] b+d$
2. $a c equiv#sub[m] b d$
    - $a c = (b+ k m)(d + l m) = b d + b(l m) + k(d m) + k l m^2 = b d + m(b l +k d + k l m) => m | (a c - b d) => a c equiv#sub[m] b d$
- *C4.15:* $a_i equiv#sub[m] b_i => f(a_1,...,a_k) equiv#sub[m] f(b_1, ..., b_k)$ if $f$ is a multivariate polynomial with integer coeffcients.


- *L4.16*
    - $a equiv#sub[m] R_m (a)$
    - $a equiv#sub[m] b <=> R_m (a) = R_m (b)$
    - C4.17: $R_m (f(a_1,...,a_k)) = R_m (f(R_m (f_1),..., R_m (f_k)))$

*L4.18: Multiplicative Inverse*
- $a x equiv#sub[m] 1$ has a solution iff $gcd(a,m)=1$. The solution is unique.
- *Calculating Inverse using Extended GCD:*
    - Find $x, y$ such that $a x + m y = gcd(a, m)$. If $gcd(a, m) = 1$, then $ a x equiv#sub[m] 1$, so $x$ is the inverse.
    - Example: Inverse of $5$ modulo $11$: 
        1. $5x + 11y = 1 <=> R_11 (5x + 11y) = R_11 (1) <=> R_11 (5x) = 1$
        2. Using Extended GCD: $x = -2 equiv#sub[11] 9$, $y = 1$.
        3. $-2 + 11 = 9$. Therefore, $5^(-1) equiv#sub[11] 9$.

*Fermats little theorem and Eulers Theorem:*

$gcd(m,a) = 1 => R_m (a^b) = R_m (a^(R_(phi(m)) (b)))$

*Thm 4.19: CRT* 

- Given: $x equiv#sub[m1] a_1, ..., x equiv#sub[mr] a_r$. 
- For relatively prime $m_1, ..., m_r$, let $M = m_1 dot ... dot m_r$.
- Let $M_i = M/m_i => M_i N_i equiv#sub[mi] 1$. Find $N_i$, the multiplicative inverse using extended Euclidian algorithm.
- Solution: $x = R_M (sum_(i=1)^r a_i M_i N_i)$

== Diffie Hellman

DH is a key-exchange protocol leveraging the discrete logarithm problem for constructing one-way functions.

#image("dh.png")

Note that this protocol requires the group $ZZ_p^*$.

= Algebra

- *Operation* on set $S$ is a function $S^n -> S$
- An *algebra* is a pair $angle.l S; Omega angle.r$ where $S$ is the set and $Omega$ is the list of operations of $S$.

== Overview of Algebraic Structures

=== Properties

- *Addition:* A1: Closure, A2: Associative, A3: Identity, A4: Inverse, A5: Commutative
- *Multiplication:* M1: Closure, M2: Associative, M3: Distributive, M4: Commutative, M5: Identity, M6: No Zero Divisors, M7: Inverse

=== Structures

- *Monoid*: A: 1, 2, 3
- *Group*: A: 1, 2, 3, 4
- *Abelian Group (Commutative Group)*: A: 1, 2, 3, 4, 5
- *Ring*: A: 1, 2, 3, 4, 5, M: 1, 2, 3
- *Commutative Ring*: A: 1, 2, 3, 4, 5, M: 1, 2, 3, 4
- *Integral Domain*: A: 1, 2, 3, 4, 5, M: 1, 2, 3, 4, 5, 6
- *Field*: A: 1, 2, 3, 4, 5, M: 1, 2, 3, 4, 5, 6, 7

== Monoids and Groups

- A *monoid* has 1) closure 2) associativity and 3) an identity.
- A *group* is a monoid with an 4) inverse.

=== Neutral Elements

*D5.3:* A left [right] neutral/identity element ($e in S$): $e * a = a [a * e = a]$. If $e * a = a * e = a$ then $e$ is the neutral element.

- *L5.1:* If LN and RN then LN = RN. Since $e * e' = e' and e * e' = e => e = e'$

=== Associativity

*D5.4:* Associative means $a*(b*c) = (a*b)*c$.

=== Inverse Elements

*D5.6:* A left [right] inverse of $a$ called $b$ is such that $b * a = e [a * e = e]$. If $a * b = b * a = e$ we simply call it inverse.

- *L5.2:* If LI and RI then LI = RI. Proof: Let $b$ be LI and $c$ be RI. Then $b = b*e = b*(a*c) = (b*a)*c = e*c = c$.

- *Uniqueness of Inverse:* $a * b = a * b' = e => b * a * b = b * a * b' = b * e => b = b' = b$
=== Group Axioms
Group: $angle.l G; *, hat, e angle.r$. 

- *L5.3:* For any group we have:
    1. $hat((hat(a))) = a$
    2. $hat(a * b) = hat(b) * hat(a)$
    3. Left cancellation: $a * b = a * c => b = c$, Right cancellation: $b * a = c * a => b = c$
    4. $a * x = b and x * a = b$ have both a unique solution for any $x,a,b$.

*Minimal axioms:*
- *G1:* associative, *G2':* RN, *G3':* RI
- First prove *G3* before proving *G2*!!!
- *G3:* $hat(a) * a = (hat(a) * a) * e = (hat(a) * a) * (hat(a) * hat(hat(a))) = hat(a) * (a * (hat(a) * hat(hat(a)))) = hat(a) * ((a * hat(a)) * hat(hat(a))) = hat(a) * (e * hat(hat(a))) = (hat(a) * e) * hat(hat(a)) ) hat(a) * hat(hat(a)) = e$
- *G2:* $a * e = a * (hat(a) * a) = (a * hat(a)) * a = e * a$

=== Group Structures

- *Direct Product (D5.9):* $angle.l G_1 times ... times G_n; * angle.r$. $*$ is component wise.

=== Homomorphisms

*D5.10:* Let $G,H$ be two groups. Let $phi: G -> H$. If we can have $phi(a *_G b) = phi(a) *_H phi(b)$ we have a group homomorphism. If $phi$ is a bijection then we have a isomorphism.


*L5.5:* 1) $phi(e_G) = e_H$ and 2) $phi(hat(a)) = hat(phi(a))$

#columns(2, [

Note that $phi$ need not be an injection, if the kernel of $phi$ (= ${a in G | phi(a) = 1}$) is non-zero, since then $phi$ can't be injective.

#colbreak()

#image("homomorphism.png", width: 100%)
])


==== How to prove isomorphism

1. Define mapping function which you suspect is an isomorphism $phi$.
2. Check if map is well defined. i.e maps to max one element
3. Check if map is totally defined. i.e maps to at least one element
4. Verify $phi(g) in H forall g in G$. i.e image of $phi$ is $subset.eq H$.
5. Check homomorphism: $phi(g_1 *_G g_2) = phi(g_1) *_H phi(g_2)$
6. Check injectivity: $phi(g_1) = phi(g_2) => g_1 = g_2$ or it's contrapositive.
7. Check surjectivity: Show that $forall h in H exists g in G (phi(g) = h)$
8. Conclude isomorphism

=== Subgroups

If $H subset.eq G$ and $H$ itself satisfies all group properties then $H$ is a subgroup of $G$. For any group ${e}$ and $G$ are trivital subgroups.

==== Order

The order of a *group* is the number of elements. The order of an *element* $"ord"(a) = m and m >= 1 <=> a^m = e$. If $not(exists "ord"(a)) => "ord"(a) = oo$. Naturally $"ord"(e)=1, "ord"(a)=2 => a^2 = e => a = a^(-1)$

*L5.6:* Each element of a finite group must have finite order.
- Since $G$ is finite we must at some point have $a^r = a^s = b and r < s "by pigeon hole" => a^(s-r) = a^s * a^(-r) = b * b^(-1) = e => exists x (x = s-r and a^x = e)$.

It follows that $a^m = a^(R_("ord"(a)) (m))$

=== Cyclic Groups

*D5.14:* $angle.l a angle.r = {a^n | n in ZZ}$. $angle.l a angle.r$ is the smallest subgroup of $G$ which contains $a$. Notice how $angle.l a angle.r = {e, a, a^2, ..., a^("ord"(a)-1)}$.

*D5.15:* If a group can be generated by an element, it's called cyclic. If $g$ is a generator, so is $g^(-1)$.

- $angle.l ZZ_n; + angle.r$ is cycle for every $n$ where $1$ is a generator. The generators of the group are all $g in ZZ_n$ where $gcd(g,n)=1$.

*Thm 5.7:* A cyclic group of order $n$ is alway isomorphic to $angle.l ZZ_n; + angle.r$ and hence commutative too.

=== Order of Subgroups

*Thm 5.8, Lagrange Thm (!!!):* $H subset.eq G => |H| "divides" |G|$.
- *C5.9:* For every finite group, the order of its element divides the group order. i.e $"ord"(a) "divides" |G| forall a in G$.
- *C5.10:* $a^(|G|) = e forall a in G$ (for finite groups). Proof: $a^(|G|) = a^(k dot "ord"(a)) = (a^("ord"(a))^k = e^k = e$.
- *C5.11:* Every group of prime order is cycle and every element except $e$ is a generator. Proof: Every subgroup divides $p => "ord"(g) = 1 or p. "ord"(g) = 1 => g = e$ otherwise any other element works.

=== Euler's Function and $ZZ_m^*$

*D5.16:* $ZZ_m^* = {a in ZZ_m | gcd(a,m) = 1}$, i.e a set of all coprime to $m$ numbers in $ZZ_m$.

*D5.17:* The Euler function is defined as $phi(m) = |ZZ_m^*|$. Can be calculated by: $m = p_1^(e_1) dot ... dot p_k^(e_k) => phi(m) = (p_1^(e_1)-p_1(e_1-1))...(p_k^(e_k)-p_k^(e_k - 1))$. E.g. $phi(60) = (2^2 - 2^1)(3-1)(5-1) = 16$.

*Thm 5.13:* $angle.l ZZ_m^*; dot.circle, ^(-1), 1 angle.r$ is a group.

*C5.14 (Fermat, Euler):* 1) $forall m >= 2 and gcd(a,m) = 1$ we have $a^(phi(m)) equiv#sub[m] 1$. 2) For every prime $p$ we have $a^(p-1) equiv#sub[p] 1 <=> a^p equiv#sub[p] a$.

*Thm 5.15:* The group $ZZ_m^*$ is cyclic iff $m = 2, m= 4, m= p^e, m= 2p^e, "where" p != 2 "and is prime" and e >= 1$.

== RSA

For RSA we need to know the following theorem following from Lagrange's theorem:

*Thm 5.16:* 
- Let $G$ be a finite group. 
- Let $e in ZZ$ be relatively prime to $|G|$. 
- The function $x arrow.r.bar x^e$ is a bijection. 
- The unique $e$-th root of $y$ such that $x^e = y <=> x = y^d$ where $d$ is the multiplicative inverse of $e$ modulo $|G|$, i.e $e d equiv#sub[|G|] 1$.
- Proof: 1) $e d = k dot |G| + 1$ 2) $(x^e)^d = x^(e d) = x^(k dot |G| + 1) = (x^(|G|)^k) dot x = x$.
- This means that $y arrow.r.bar y^d$ is the inverse function of $x arrow.r.bar x^e$.

*Protocol:*

#image("rsa.png")

The idea is as follows:
1. Let $n = p dot q$.
2. Let $f = |ZZ_n^*| = (p-1)(q-1)$
3. Choose some $e$ and calculate $d equiv#sub[f] e^(-1)$ using Ext. Eucl. algorithm.
4. Make $n, e$ public.
5. The message $m$ can be encrypted by $m arrow.r.bar c = R_n (m^e)$.
6. The decryption can be done by $c arrow.bar m = R_n (c^d)$.

== Rings and Fields

- A *ring* is an additive abelian group with 1) multiplicative closure 2) multiplicative associativity 3) distributivity
- A *commutative ring* is a ring with 4) commutativity
- An *integral domain* is a commutative ring with 5) a multiplicative identity and 6) no zero divisors
- A *field* is an integral domain with 7) multiplicative inverses

*L5.17: For any ring $angle.l R; +,-,0,dot,1 angle.r$*
1. $0 a = a 0 = 0$. Proof: $0 = - (a 0) + a 0 = -(a 0)+a(0+0) = (-(a 0)+a 0) + a 0 = 0 + a 0 = a 0$. $0a$ gets proven in a similar manner.
2. $(- a) b = -(a b)$. Proof: $(-a)b+a b = (-a + a)b = 0 b = 0 => (-a)b = -(a b)$
3. $(-a)(-b) = a b$. Proof: $(-a)(-b) = -(a(-b)) = -(-(a b)) = a b$
4. If $|R| > 1 => 1 != 0$. Proof by contradiction: Let $a, b$ be distinct elements. Then $a = a*1 = a*0 = 0 and b = ... = 0 => a = b$ which contradicts our precondition.

*Characteristic of a Ring (D5.19):* Order of $1$ in the additive group if finite, 0 otherwise. Hence the characteristic in the ring $ZZ_m$ is $1$ and in $ZZ$ 0.

=== Units and Multiplicative Group

*D5.20:* An element of a ring $u in R$ is called *unit if it's invertible*, i.e $exists v in R (u v = v u = 1)$, $v = u^(-1)$. The set of units is $R^*$.
- Examples: $ZZ^* = {1,-1}, RR^* = RR backslash {0}, "Gaussian Integers"^* = {1, -1, i, -i}$

*L5.18:* For a ring $R, R^*$ is a multiplicative group.
- Proof: We need to show that $forall u, v exists y ( y = (u v)^(-1)) => y = v^(-1) u^(-1)$. $1 in R^*$ since $1 = 1^(-1)$. Associativity is inherited from $R$.

=== Divisors

*D5.21:* $exists c in R ( b = a c) => a divides b$. Where $R$ is a commutative ring.

*L5.19:* 1) $divides$ is transitive. 2) $a divides b => a divides (b c)$ 3) $a divides b and a divides c => a divides (b + c)$

*D5.22:* The GCD definition is identical as in number theory, just using the divides definition from above (L5.19).

=== Zero Divisors and Integral Domains

*Zero Divisor (D5.23):* $a != 0 and exists b (b != 0 and a b = 0) => a divides 0$. $a$ is called a zerodivisor of that commutative ring.

*Integral Domain (D5.24):* An integral domain $D$ is a non-trivial ($|D| > 1$) commutative ring without zerodivisors. _Examples:_ $ZZ, QQ, RR, CC$, _Non Examples:_ $ZZ_m$ if $m$ isn't prime, any element not relatively prime to $m$ is a zerodivisor.

*L5.20:* In an ID $a divides b => exists c (b = a c)$ then that $c = b/a$ is unique. Proof: $0 = a c - a c' = a (c + -c') => c + -c' = 0 => c = c'$.

=== Polynomial Rings

*Thm 5.21:* For any commutative ring $R, R[x]$ is a commutative ring too.

*L5.22:* Let $D$ be an ID, then:
1. $D[x]$ is an ID. Proof: If there were zerodivisors then for $p(x)q(x) = 0$ the polynomial coefficients would need to be zerodivisors, cause otherwise we'd never get $=0$.
2. $deg(a b) = deg(a) + deg(b)$. Proof: Similar to (1), since we don't have zerodivisors the highest degree can't simply disappear and hence must be present.
3. Units of $D[x]$ are constants that are units of $D$. i.e $D[x]^* = D^*$. Proof: We need to get a polynomial where only the constant coefficient is $=1$, the others must $=0$. Now since we don't have zerodivisors we can only have units by inheriting them from $D$.

=== Fields

*D5.26:* A *field* is a non-trivial commutative ring $F$ where every non-zero element is a unit, i.e is invertible. _Examples:_ $QQ, RR, CC$. _Non Examples:_ $ZZ, R[x] ("for any arbitrary rings")$.

*Thm 5.23:* $ZZ_p$ is a field iff $p$ is prime.

*Thm 5.24:* A field is an integral domain. Proof: It suffices to show that a unit is not a zerodivisor. Assume $u v = 0 => v = 0 "since" v = 1v = u^(-1) u v = u^(-1) 0 = 0$. Hence $u$ is not a zerodivisor.

=== Polynomials over a Field

*D5.27:* A polynomial is called a *monic* if the leading coefficient is 1.

*D5.28:* A polynomial with degree $>= 1$ is *irreducible* if it is only divisible by constants or constant multiples of itself. Similar to primality.

*D5.29:* The monic polynomial of largest degree such that $g(x) divides a(x) and g(x) divides b(x) => g(x) = gcd(a(x), b(x))$.


=== Division in Fields

*Thm 5.25:* $a(x) = b(x) dot q(x) + r(x)$.

=== Roots

*D5.33:* Let $a(x) in R[x]$. An element $alpha in R$ s.t. $a(alpha) = 0$ is called a root of $a(x)$.

*L5.29:* For $alpha in F (a(alpha) = 0 <=> (x-alpha) divides a(x))$
- *$arrow.r.double$:* Assume $a(alpha) = 0$. Then $a(x) = (x-alpha)q(x) + r(x)$ where $deg(r(x)) < deg(x-alpha) = 1 => r(x) "is a constant" => r = a(x) - (x-alpha)q(x)$. Now if $x=alpha => r = 0 - 0 dot q(alpha) = 0$. Since $r = 0$ we know that $a(x) = (x-alpha)q(x) => (x-alpha) divides a(x)$
- *$arrow.l.double$:* Assume $(x-alpha) divides a(x) => a(alpha) = (alpha-alpha)q(alpha) = 0 => alpha "is a root"$
- Note that this implies that an irreducible polynomial of degree $>= 2$ has no roots.

*C5.30:* A polynomial of degree 2 or 3 over a field is irreducible iff it has no root. Proof: A reducible polynomial has a factor of degree 1 and hence a root.

*Thm 5.31:* A non-zero polynomial $a(x) in F[x]$ of degree $d$ has atmost $d$ roots.
- Proof: To show contradiction assume $a(x)$ has degree $d$ but $e > d$ roots, then $product_(i = 1)^e divides a(x)$ by Lemma 5.29, but then becomes a polynomial of degree $e$ instead.

=== Polynomial Interpolation

*L5.32:* A polynomial $a(x) in F[x]$ of degree $d$ can be uniquely determined by any $d+1$ values (!!!) of $a(x_i)$ s.t. $x_i$ are distinct.
- Proof by construction: Assume $beta_i = a(alpha_i)$ for $i in [1, d+1]$
- $a(x) = sum_(i = 1)^(d+1) beta_i u_i (x)$ where $u_i (x) = (x-alpha_1)/(alpha_i - alpha_1) dot ... dot (x-alpha_(i-1))/(alpha_i - alpha_(i-1)) (x-alpha_(i+1))/(alpha_i - alpha_(i+1)) dot ... dot (x-alpha_(d+1))/(alpha_i - alpha_(d+1))$
- $u_i (x)$ is well defined since $a_i - a_j != 0 "iff" i != j$ and hence is invertible. We also naturally agree with the given values. $a(x)$ has degree of at most $d$.
- Uniqueness: Assume $a != a' and in O(x^n)$ are interpolated by the same $d+1$ points. To show contradiction let $b = a' - a != 0$. $b$ must be $in O(x^n)$ by Thm 5.31, however all $d+1$ points are valid roots of $b$ (contradiction), hence $b = 0 => a = a'$.

== Finite Fields

$"GF"(p) equiv ZZ_p$ is a basic finite field. Recall $F[x]$ (coefficients are field elements) is analogous to $ZZ$. Now we can define $F[x]_(m(x))$. 

*D5.34:* $F[x]_(m(x)) = {a(x) in F[x] | deg(a(x)) < d}$ 

- *L5.33:* Congruence mod $m(x)$ is an equivalence relation on $F[x]$ where each equivalence class has a unique rep of deg $< deg(m(x))$.
- *L5.34:* $|F[x]_(m(x)) = |F|^deg(m)$
- *L5.35:* $F[x]_(m(x))$ is a ring with respect to addition and multiplication $mod m(x)$.
- *L3.36:* $a(x)b(x) equiv_(m(x)) 1$ iff $gcd(a,b)=1$
- *Thm 5.37:* A ring $F[x]_(m(x))$ is a field iff $m(x)$ is irreducible.

== Error Correcting Codes

*Idea:*
- Let $cal(A)$ represent our alphabet. A msg of length $k$ is $M in cal(A)^k, (a_0, ..., a_(k-1)) = M$. 
- Now we create a polynomial $a(x)$ with coefficients parameterized using these values. We now evaluate $n > k$ points in $a(x)$.
- Now to reconstruct $a(x)$ we can only need $k+1$ points, which means $n-k+1$ can be "lost" and we should still know how to recover the msg.
*Definitions:*
- *D5.35:* Let's define encoding function $E: cal(A)^k -> cal(A)^n: (a_0,...,a_(k-1)) arrow.bar.r E((a_0,...,a_(k-1))) = (c_0,...,c_(n-1))$. $E$ is an injection because $n > k$ and the output is called "codeword". 
- *D5.36:* $C = "Im"(E)$ since we have an injection think of $C$ as the reachable space $in cal(A)^n$. This is called the set of codewords aka an error correcting code. $|C| = |cal(A)|^k$ 
- *Hamming Distance (D5.37):* Basically char diff between two equal length strings.
- *D5.38:* The minimum distance of an error-correcting code $C$ denoted $d_min (C)$ is the minimum Hamming distance between any two codewords.
Now suppose Alice sends Bob the codeword $C$. The error correcting capability can be characterized by the number of errors $t$ which can be corrected.
- *D5.40:* A decoding function $D$ is t-error correcting for $E$ for ANY $M in cal(A)^k$. $D((r_0,...,r_(n-1))) = (a_0,...,a_(k-1))$ for any input with at most $t$ Hamming distance from $E$. A code $C$ is $t$-error correcting if there $exists E, D : C = "Im"(E) and D "is t-error correcting"$ 
- *Thm 5.41:* A code $C$ with $d_min (C) = d$ is $t$-error correcting iff $d >= 2t + 1$. 
    - $arrow.l.double$: Take any two codewords with Hamming dist of $2t + 1$. Now corrupt both words $t$ times each. Now you still have a distance of $1$ with which you can identify the nearest source and hence reconstruct the information completely.
    - $arrow.r.double$: If two codewords differ in $<= 2t$ positions then there exists a word in the middle, i.e. with equal distance to both codewords, hence it's possible that $t$ errors cannot be uniquely corrected. Hence they need to differ by $2t + 1$

We call these: $(n, k)$-error-correcting code.

= Proof Systems

- *Syntactic objects* are finite strings over some alphabet: $Sigma^*$. Objects such as statements and proofs can be syntactically represented using such a string.
- *Statement:* $S subset.eq Sigma^*$, *Proof:* $P subset.eq Sigma^*$. 
- We define a truth function $tau: S -> {0,1}$ which gives us the (god given) truth of a statement. For a $s in S, tau(s)$ defines the meaning, called *semantics* of the object in $S$. 
- An element $p in P$ either is a valid proof for a statement $s in S$ or not. This can be defined by the *verification function* $phi: S times P -> {0,1}$ where $phi(s,p) = 1$ means $p "is a valid proof for" s$. $phi$ needs to be efficiently computable.
- *Proof System:* A proof system is a quadruple $Pi = (S, P, tau, phi)$
- *Soundness:* $forall s in S exists p in P (phi(s, p) = 1 => tau(s) = 1)$. Meaning if we say a statement is true using a provided proof, it actually is true.
- *Completeness:* $forall s in S (tau(s) = 1 => exists p in P (phi(s, p) = 1))$. Meaning for all true statements, we can provide a proof showing such.

= Logic

The goal of logic is to provide a specific proof system $Pi = (S, P, tau, phi)$ for which a very large class of mathematical statements can be expressed as an element of $S$.

Such a proof system can _never_ capture all possible statements, in particular about the proof system itself (paradoxical).

In logic $s in S$ consists of a formula and/or a set of formulas. A proof consists of *syntactic derivation* steps. Such steps consist of applying syntactic rules. The set of allowed rules is called *calculus*. 

- The *syntax* of logic defines an alphabet $Lambda$ and specifies which strings in $Lambda^*$ are formulas (syntactically correct).
- The *semantics* of logic defines:
    - A function *free* which takes a formula and returns a set of indices of free symbols (variables).
    - An *interpretation* consists of $Z subset.eq Lambda$, a set of possible values (domain) for each symbol in $Z$, and a function assigning each symbol in $Z$ a value in its associated domain. Often (not in propositional logic) the domain is defined by a universe $U$. 
    - An *interpretation is suitable* for a formula $F$ if each free variable is assigned a value.
    - A function $sigma$ assigning each formula $F$ and each interpretation $A$ suitable for $F$ a truth value $sigma(F, A) in {0,1}$. We often write $A(F)$ instead and call this the truth value of $F$ under interpretation $A$. 
- A suitable interpretatin $A$ for which $sigma(F, A) = 1 "or" A(F) = 1$ is called a model for $F$, one writes $A models F$. The same can be done for a set of formulas.

== Satisfiability, Tautology, Consequence, Equivalence

- A formula $F$ or a set of formulas $M$ is *satisfiable* if there exists a model for $F ("or" M)$. Unsatisfiable otherwise (denoted $bot$). 
- A formula $F$ is a *tautology* or *valid* if it is true for every suitable interpretation (denoted $top$).
- A formula $G$ is a *logical consequence* of $F$ if every interpretation suitable for both $F, G$ which model $F$ also model $G$, denoted $F models G$.
- $F, G$ are *equivalent* ($F equiv G$) if for every interpretation suitable for both $F,G$ they yield the same truth value for $F, G$. $F equiv G <=> F models G "and" G models F$. 
- A set $M$ of formulas can be interpreted as the conjunction (AND) of all formulas.

=== Logical Consequence vs Unsatisfiability

- *L6.2:* $F$ is tautology iff $not F$ is unsat.
- *L6.3:* The following are equivalent:
    1. ${F_1, ..., F_k} models G$
    2. $(F_1 and ... and F_k) -> G$ is a tautology
    3. ${F_1, ..., F_k, not G}$ is unsat.

== Logical Operators
- *D6.16:* 
    - $A((F and G)) = 1$ iff $A(F) = 1 "and" A(G) = 1$
    - $A((F or G)) = 1$ iff $A(F) = 1 "or" A(G) = 1$
    - $A(not F) = 1$ iff $A(F) = 0$

== Hilbert-Style Calculi

- *D6.17:* A *derivation rule* or *inference rule* ${F_1,..., F_k} tack.r_R G$ is a syntactic step.
- *D6.19:* A *logical calculus* $K$ is a finite set of dervation rules $K = {R_1, ..., R_m}$. 
- *6.20:* A *derivation* of a formula $G$ from a set $M$ in calculus $K$ is finite sequence of derivation rules applied on $M$ leading to $G$. We write $M tack.r_K G$ if there is such a derivation.

== Soundness and Completeness of a Calculus

- *D6.22:* A calculus $K$ is *sound* if for every set $M$ and every $F$: $M tack.r_K F => M models F$. Meaning if $F$ is derived from $M$ then $F$ is a logical consequence of $M$. Similarly $K$ is *complete* if $M models F => M tack.r_K F$. 

== Normal Forms

=== Prenex Normal Form

All quantifiers are at the beginning. Every formula in predicate logic can be converted into PNF form. Build a tree and let the quantifiers "bubble up". 

=== Skolem Normal Form

The SNF *doesn't* preserve logical equivalence but preservers satisfiability. We want to eliminate existance quantifiers.
*Process:*
1. First convert to PNF.
2. Eliminate existance quantifiers. If we have $forall a, b, c exists y$ then we replace $y$ by $f(a,b,c)$. 

=== Conjunctive Normal Form

The CNF of a formula is the conjunction (AND) of disjunctions (OR) of literals ($= x "or" not x$). $F = (a or b or c) and (a or not b or not c) and ...$. Construct by making truth table. For each row evaluating to 0, take the disjunct *negation* of that row ($A = 0, B = 1 equiv 0 => (not A or B)$). 

=== Disjunctive Normal Form

The DNF of a formula is the disjunction (OR) of conjunctions (AND) of literals. Construct by looking at rows evaluating to 1 and take those ($A = 0, B = 1 equiv 1 => (not A and B)$). 

== Resolution Calculus

- *D6.28:* A *clause* is a set of literals.
- *D6.29:* The set of clauses for a formula in CNF $F = ((a or ... or f) and ... and (x or ... z))$ is $K(F) = {{a,...f},...,{x,...,z}}$. For sets $M$ we unionize the clauses of the individual formulas. 
- A clause $K$ is *resolvent* of $K_1, K_2$ if there is a literal $L$ s.t. $L in K_1 and not L in K_2 => K = (K_1 backslash {L}) union (K_2 backslash {not L})$
- *Unsat:* If we can derive the empty clause denoted ${}$ from a clause set using the resolution rule, then the original clause set is unsatisfiable.
- *Empty clause set:* An empty set of clauses is always satisfiable and hence a tautology and also always false and unsatisfiable (both vacuously)

== Predicate Logic (First-order Logic)

=== Syntax

- Variable symbol $x_i$
- Function symbol $f_i^((k))$
- Predicate symbols $P_i^((k))$
- Term, defined recursively: 1) Variable is a term 2) If $t_1,...,t_k$ are terms then $f(t_1, ..., t_k)$ is a term.
- Formula, defined recursively: 1) $P(t_1, ..., t_k)$ is a formula. 2) $F$ and $G$ are formulas then $not F, (F and G), (F or G)$ are each formulas. 3) If $F$ is a formula, then $forall x_i F, exists x_i F$ are formulas.

=== Semantics

The interpretation is a tuple $A = (U, phi, psi, xi)$. 
- $U$ is a universe. $phi$ assigns each function symbol a semantic function. $psi$ assigns each predicate symbol a predicate function. $xi$ assigns each variable symbol a value.
- We write $U^A$ or $f^A$ or $P^A$ or $x^A$ instead. 
- *D6.36:*
    - The value $A(t)$ of term $t$ is defined as follows:
        - If $t$ is a variable $=x_i$, then $A(t) = x_i^A$- If $t$ is of the form $f(t_1,...t_k)$, then $A(t) = f^A (A(t_1), ..., A(t_k))$. 
    - The truth value of a formula $F$ is defined recursively by D6.16 and:
        - If $F$ is of the form $P(t_1,...,t_k)$ then $A(f) = P^A (A(t_1), ..., A(t_k))$ 
        - If $F$ is of the form $forall x G$ or $exists x G$ then let $A_[x -> u]$ for $u in U$ be the same structure as $A$ except $x^A$ is overwritten by $u$:
            - $A(forall x G) = cases(1 "if" A_[x -> u] (G) = 1 "for all" u in U, 0 "else")$
            - $A(exists x G) = cases(1 "if" A_[x -> u] (G) = 1 "for some" u in U, 0 "else")$

*L6.7:* For any formuas $F, G$ and $H$ where $x$ doesn't occur free in $H$ we have:
1. $not(forall x F) equiv exists x not F$
2. $not(exists x F) equiv forall x not F$ 
3. $(forall x F) and (forall x G) equiv forall x (F and G)$
4. $(exists x F) or (exists x G) equiv exists x (F or G)$
5. $forall x forall y F equiv forall y forall x F$
6. $exists x exists y F equiv exists y exists x F$ 
7. $(forall x F) and H equiv forall x (F and H)$
8. $(forall x F) or H equiv forall x (F or H)$
9. $(exists x F) and H equiv exists x(F and H)$
10. $(exists x F) or H equiv exists x (F or H)$

*L6.8:* If one replaces a subformula $G$ of a formula $F$ by an equivalent to $G$ formula H, then the resulting formula is equivalent to $F$. 

==== Substitution of Bound Variables

*L6.9:* For a formula $G$ in which $y$ doesn't occur:
- $forall x G equiv forall y G[x"/"y]$
- $exists x G equiv exists y G[x"/"y]$ 

= Helpful Stuff

#image("eulers_totient.jpg")

For $ZZ_a times ZZ_b$ is cyclic iff $gcd(a,b) = 1$. 
