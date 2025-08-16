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
  let font_size = 9pt
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

  columns(3, gutter: 2mm, body)
}

#show: knowledge-key.with(
  title: [Linear Algebra HS24],
  authors: "cs.shivi.io",
)

// #set text(font: "New Computer Modern")
// #show sym.emptyset: set text(font: "Fira Sans")
#show math.equation.where(block: true) : set align(left)
#import "@preview/codelst:2.0.1": sourcecode

= Basics

== Types of combinations

- *Affine:* $sum lambda_i = 1$ (think infinite line $mu (u-v)$)
- *Conic:* $lambda_i >= 0$ (think positive subsection in direction of $u and v$)
- *Convex:* Affine $and$ Conic (think intersection)

== Norms

Assigns _non-negative_ "sizes" to vectors.

- *1-Norm:* $sum abs(v_i)$ (measures travelled dist along axis)
- *2-Norm (Euclidian):* $sqrt(sum v_i^2)$ (geometric distance)
- *p-Norm (Generalization):* $root(p, (sum v_i^p))$
- *Max-Norm:* $max{v_i}$

Other:
- $norm(v)^2 = v dot v$
- $norm(1_n) = sqrt(n)$

== Scalar Products

*Euclidian:* $u dot v := u^T v$

Satisfy:
- $a dot (b + c) = a dot b + a dot c$ (linear in second factor)
- $a dot (lambda b) = lambda (a dot b)$ (linear in second factor)
- $a dot b = b dot a$ (symmetric for $RR$) and $a dot b = b^H dot a^H$ (hermitian for $CC$)
- $forall a in V : a dot a (> 0) or (= 0 "iff" a = 0)$ (positive definite)

Other:
- $(x dot y)^2 <= (x dot x) (y dot y)$

== Angles
Given $u, v in RR^n$ and $u' = u/norm(u), v' = v/norm(v)$ unitized vectors: $cos(alpha) = u' dot v'$.

$sin: 0 arrow.bar.r sqrt(0)/2, 30 arrow.bar.r sqrt(1)/2, 45 arrow.bar.r sqrt(2)/2, 60 arrow.bar.r sqrt(3)/2, 90 arrow.bar.r sqrt(4)/2$

== Inequalities
=== Cauchy-Schwarz

$
abs(u dot v) <= norm(u) norm(v), -1 <= (u dot v)/(norm(u) norm(v)) <= 1, - norm(u) norm(v) <= u dot v <= norm(u) norm(v)
$

=== Triangle

$norm(a + b) <= norm(a) + norm(b)$, meaning the direct way is always $<=$ the indirect way.

== Linear In/Dependence

*Linear Dependence Equivalent Definitions:*
1. $exists u in V : u in "span"{V backslash {u}}$ (vector can be represented using others)
2. $0 in "span"(V)$ (0 combination)
3. $exists v_i in V : v_i in "span"{V_(1...i-1)}$ (vector can be represented by previous vectors)

== CR Decomposition

$C:$ independent columns, $R:$ combinations to get back to $A$. Basically run RREF on $A$ and put identity columns into $C$ and copy RREF without the ending zero-rows into $R$.

= Matrices and Linear Transformations

Given a matrix in $RR^(m times n)$ ($m$ rows, $n$ columns), think of a function $f: RR^n -> RR^m$ and how it possibly compresses information...

== Linear Transformations

- Definition: $T(lambda a) = lambda T(a)$ and $T(a + b) = T(a) + T(b)$
- Quick Checks: $T(0) = 0$ and $T(a x + b y) = a T(x) + b T(y)$. Basically check Homomorphism.

Any linear transformation can be represented by a matrix: $A = mat(
  |, ..., |;
  T(e_1), ..., T(e_n);
  |, ..., |;
)$.

== Spaces

For square we have: 1) Identity, 2) Diagonal 3) Upper/Lower 4) Symmetric ($A^H = A$)

- *Rank:* $"rank"(A) = "number of independent vectors"$. (Fullrank iff intertible for square matrices)
  - $"rank"(A) = "rank"(A^T) = "rank"(A^T A) = "rank"(A A^T)$
- *Column Space:* $C(A) = {A x | x in RR^n} subset.eq RR^m$, aka *Image*. $dim = r$
- *Row Space:* $R(A) = C(A^T) = {A^T x | x in RR^m} subset.eq RR^m$. $dim = r$
- *Null Space:* $N(A) = {x in RR^n | A x = 0}$. aka *Kernel*. $dim = n - r$.
- *Left Null Space:* $"LN"(A) = N(A^T) = {x in RR^m | x^T A = 0^T "or" A^T x = 0}$. $dim = m - r$

A *basis* is defined as an independent set which spans your space. The dimension of a space is the cardinality of your basis for that space (which stays same independent of which basis represents that space).

== Don't Forget

- $A B != B A$
- $(A B)^(-1) = B^(-1) A^(-1)$
- $(A B)^T = B^T A^T$

= Systems of Linear Equations

Basically $A x = b$.

== LU Decomposition

Run REF on $A in RR^(m times n)$ to generate $U in RR^(m times n)$ and track coefficients in $L in RR^(n times n)$, where $L$ contains $1$'s on the diagonal and the opposite values of the operations performed on the corresponding rows.

== Permutation Matrices

- Each row and column have exactly one 1.
- They are orthogonal, hence $P^(-1) = P^T and P P^T = P^T P = I$
- $det(P) = plus.minus 1$
- $P = P_1 P_2$ is also a permutation matrix
- A permutation creates a bijection from $[n] -> [n]$.

== LUP Decomposition

$P A = L U$. If $U = E_(m-1) P_(m-1) E_(m-2) P_(m-2) ... E_(1) P_(1) A => P = P_(m-1) dot ... dot P_1$

= Vector Spaces

A vector space is an algebra $(V, +, dot)$, where $+: V times V -> V, dot: RR dot V -> V$ s.t. we have 1) commutativity 2) associativity 3) a zero vector 4) a negative vector 5) identity element $in RR$ 6) compatibility of $dot in RR and dot in VV$ 7) distributivity over $+ in VV$ and 8) distributivity over $+ in RR$

== Subspace

$U subset.eq V$ is a subset if we have 1) closure under $+: U times U -> U$ and 2) closure under $dot: RR times U -> U$.


=== Columns Space

See definition above. Construct by running RREF on $A$ and select the columns of $A$ based on the pivot columns of RREF. *Note:* R/REF changes the columnspace, make sure to pick from $A$.

=== Row Space

See definition above. Construct by running RREF of $A$ and selecting all non-zero rows of that RREF. *Note:* R/REF doesn't change rowspace, make sure to pick from R/REF.

*Lemma 4.27:* Given an invertible matrix $M$ then $R(A) = R(M A)$ (left multiplication only).

=== Nullspace

See definition above. $N(A) subset.eq RR^n$. Construct by running RREF on $A$. For each non-pivot column set it's coefficient $=1$ and find out what the coefficients of the pivot columns must be to get $0$. This should yield $n-r$ columns forming a basis of $N(A)$.

*Lemma 4.33:* Given an invertible matrix $M$ then $N(A) = N(M A)$.

=== Left Nullspace

See definition above. $"LN"(A) := N(A^T) subset.eq RR^m$

== Solution Space

For any $A x = b$ we have three options: 1) No solution 2) One solution 3) Infinite solutions.

- If $A$ is not invertible and $b in.not C(A)$ then no solution can exist.
- If $A$ is invertible $=> N(A) = {0}$ then exactly one solution exist $x = A^(-1) b$
- If $A$ is not invertible but $b in C(A)$ then $exists x : A x = b "and" forall n in N(A) : A (x + n) = b + 0 = b$. This can happen when our transformation $f$ is going from a higher dimensional space to a lower dimensional space, i.e $n > m$.

#image("solutions.png", width: 60%)

*Inverse Theorem 3.11:* Let $A in RR^(m times m)$, then the following are equivalent:
1. $exists A^(-1)$
2. $forall b in RR^m exists x : A x = b$, and $x$ is unique
3. The columns of $A$ are independent

= Orthogonality

*Definition:* $u$ is orthogonal to $v$ if $u dot v = 0$. Two subspaces $U, V$ are orthogonal if $forall u in U forall v in V : u dot v = 0$. A basis can be used to check orthogonality.

*Theorem 5.1.7:* Let $V, W$ be subspaces of $RR^n$, then the following are equivalent:
1. $V = W^bot$
2. $dim(V) + dim(W) = n$
3. $forall u in RR^n exists "unique" v, w : u = v + w$

== Four fundamental Subspaces

- $N(A) = R(A)^bot$
  - Think how if $A x = 0$ then each row of $A$ "dotted" by $x = 0$, which means these $x$'s are orthogonal to each row and hence the rowspace of $A$.
- $"LN"(A) = C(A)^bot$
  - Argue with the same as above but just use $A^T$ instead.

== Properties

- $Q$ is orthogonal (more like orthonormal) iff $Q^T Q = I$
- For square matrices $Q Q^T = I$ and $Q^T = Q^(-1)$
- For non-square matrices $Q Q^T = I$ may _not_ hold.
- Orthonormal matrices preserve *norm* (i.e $det(Q) = plus.minus 1$ and $norm(Q x) = norm(x)$)
- Orthonormal matrices preserve *angle*.
- $A^(-1)$ is orthonormal. $A B$ is orthonormal (since $(A B)(A B)^T = A B B^T A^T = I$)

== Gram-Schmidt

We are given $A$ a basis for some space and want to orthonormalize into $Q$.
*Steps:*
1. Normalize $v_1 -> q_1$
2. Subtract projection from previous vectors from current vector:
  1. $v'_n = v_n - sum_(i = 1)^(n-1) "proj"_(q_i) (v_n) = v_n - sum_(i = 1)^(n-1) ((v_n dot q_i) q_i)$
  2. $q_n = v'_n/norm(v'_n)$

== QR Decomposition

$A = Q R => Q^T A = R$. Basically run Gram-Schmidt on $A$ to generate $Q$ and calculate $R$.

- $R$ is upper triangular and invertible
- $C(Q) = C(A)$


= Projections

The projection of $b in RR^m$ onto a subspace $S in RR^m$ is the point in $S$ that's closest to $b$. i.e $"proj"_S (b) = "argmin"_(p in S) norm(b-p)^2$ (yes error squared.)

- *1D Case:* Let $a in RR^m$ span $S$. Then $"proj"_S (b) = (a a^T)/(a^T a) b$
- *ND Case:* Let $S = C(A)$ and $b in RR^m$. Then $"proj"_S (b) = A hat(x)$ s.t. $A^T A hat(x) = A^T b$. 
  - If $b in S "iff" A x = b$ then $hat(x)$ preserves the $x$.
  - Otherwise $hat(x)$ minimizes the least square error.

*Theorem 5.2.6:* Let $S = C(A)$, then $"proj"_S (b) = P b$ s.t. $P = A (A^T A)^(-1) A^T$.

Other:
- $P^2 = P$ (projecting multiple times doesn't change the projection).
- If $"proj"_S (b) = P b$ then $"proj"_(S^bot) (b) = (I - P) b$
- $(I-P)^2 = I - P$ (since projecting onto the orthogonal complement multiple times doesn't change anything)

== Least Squares

Assume $A x = b$ does not always have a solution, however we want to get the "best" solution according $min_(x' in RR^n) norm(A x' - b)^2$. We can solve this using projections as follows:

- First write down the equation in form of e.g $b_i = lambda_3 x^3 + lambda_2 x^2 + lambda_1 x + lambda_0$
- Now write using matrices: $mat(|, ..., |; x_i^3, ..., 1; |, ..., |) vec(lambda_3, dots.v, lambda_0) = vec(b_1, dots.v, b_m)$
- Normal Equations: $(A^T A) x' = (A^T b) => N x' = y => x' = N^(-1) y$

= Pseudoinverse

- *Left Pseudoinverse:* $A^dagger A = I$
- *Right Pseudoinverse:* $A A^dagger = I$

== Left Pseudoinverse for Full Column Rank

Use a left pseudoinverse for $f: RR^n -> RR^m "s.t." n < m$, meaning we are transforming from a smaller space to a larger space. This means that we are not loosing information from the input space but we cannot represent the whole output space, meaning $b$ will probably not lie in $C(A)$ ($A$ is a basis and has full column rank), hence we basically do least squares since the system is *overdetermined*. 

Hence $A^dagger_"left" = (A^T A)^(-1) A^T ) => A^dagger A = I$

== Right Pseudoinverse for Full Row Rank

Use right pseudoinverse for $f: RR^n -> RR^m "s.t." n > m$, meaning we are transforming from a larger space to a smaller space and hence loosing information. This makes the system underdetermined (many possible solutions). This means that there exist a non-trivial nullspace. Here the right-pseudoinverse minimizes the norm of our solution.

Hence $A^dagger_"right" = A^T (A A^T)^(-1) => A A^dagger = I$

== Left Pseudoinverse for General Matrices

For general matrices $A$ the left pseudoinverse cannot be defined as $A^dagger = (A^T A)^(-1) A^T$ because $(A^T A)^(-1)$ might not be defined. Hence we need to use a different approach.

Basically we do a CR decomposition since $C$ has full-column rank and $R$ has full row rank. $A = C R => A^dagger = (C R)^dagger = R^dagger C^dagger = R^T (R R^T)^(-1) (C^T C)^(-1) C^T$

This satisfies that for $A x = b => hat(x) = A^dagger b$ and $hat(x)$ is the unique solution satisfiying $min_(x in RR^n) norm(x) "s.t." A^T A x = A^T b$.

$A^dagger$ can be defined (using SVD) as $V Sigma^dagger U^T$ where $Sigma^dagger$ is taking the reciprocal of non-zero singular values and then transposing the matrix.

= Farkas Lemma

Farkas Lemma provides a way to determine if a system of linear inequalities is feasible. It essentially states that exactly one of two alternatives is true.

*Geometric Intuition:* Imagine a cone formed by the vectors representing the inequalities. Farkas Lemma helps determine if a given vector b is inside this cone (feasible system) or if there's a hyperplane separating b from the cone (infeasible system).

Given $A in RR^(m times n)$ and $b in RR^m$ one and exactly one of these statements is true:
1. *Feasibility:* $exists x in RR^n "s.t." A x <= b and x >= 0$ (there exists a non-negative solution)
2. *Infeasibility Certificate:* $exists y in RR^m "s.t." A^T y >= 0 and y >= 0 and b dot y < 0$ (There's a non-negative linear combination of the inequalities that leads to a contradiction)

== Fourier-Motzkin Elimination

Basically we want to go from $m$ inequalities with $n$ variables to possibly $m^2/4$ inequalities with $n-1$ variables. Geometrically this is analogous to projecting the shadow of our "cone" from $n$-D to $n-1$-D.

1. We seperate the variable we want to eliminate onto say the LHS. 
2. We make sure the inequality direction is consistent for all equations.
3. We normalize the equations so that the coefficients (of the variable we want to eliminate) are $0 or plus.minus 1$
4. We get a new set of equations by combining the $+ x_i$ equations with $- x_i$ equations.
5. Repeat until we get to a low dimension case
  1. If we have an inconsistency, quit.
  2. Otherwise backsubstitute values to get a possible $x$ which satisfies the equation.

= Determinants

For 2x2: $det(mat(a,b;c,d;)) = a d - b c$. 
For NxN: (Cofactors:) Make $+-+...$ grid. Pick a row/column and calculcate $plus.minus A_(i,j) det(...)$ recursively.

*Quadratic Formula:* Either complete the square or $ x = (-b plus.minus sqrt(b^2- 4a c))/(2a) $

== Properties

*Fundamental:*
1. $det(I) = 1$
2. If we swap the rows of $A -> B$ once, then $det(B) = - det(A)$.
3. The determinant is a linear function of each row separately.
  1. If a row of $A$ is multiplied by a scalar $t$, then $det(A') = t det(A)$.
  2. If a row of $A$ is replaced by the sum of itself and a multiple of another row, the determinant is unchanged.

*Derived:*
4. If any two rows are equal then $det(A) = 0$
5. If $A$ has a row of zeros then $det(A) = 0$
6. Subtracting a multiple of one row from another row leaves the determinant unchanged.
7. If A is triangular (upper or lower), the determinant is the product of the diagonal entries.
8. $det(A) = 0$ if and only if $A$ is singular (not invertible)
9. $det(A B) = det(A)det(B)$
10. $det(A^(-1)) = 1/det(A)$
11. $det(A) = det(A^T)$

// #colbreak()

= Complex Numbers

#columns(2, [
Let $z = (a + b i) in CC$.
*Conjugate:*
- $overline(z) = a - b i$
- $z overline(z) = norm(z) = a^2 + b^2$
- $overline(x + y) = overline(x) + overline(y)$
- $overline(x y) = overline(x) overline(y)$
*Norm:*
- $norm(z) = sqrt(a^2 + b^2) in RR$
- $norm(x y) = norm(y) norm(y)$
- $norm(z^n) = norm(z)^n$

*Hermitian of a matrix:* 
Basically transpose and conjugate each entry.

#colbreak()

*Properties:*
- $z + overline(z) = 2 Re(z) = 2 a$
- $z - overline(z) = 2i Im(z) = 2i b$
- $norm(z) = norm(overline(z))$
- $z^(-1) = overline(z)/norm(z)^2$ (multiplicative inverse)
- *Triangle Inequality:* $norm(x + y) <= norm(x) + norm(y)$

*Eulers Formula:*
- $e^(i theta) = cos theta + i sin theta$
- $theta = arctan(Im(z)/Re(z)) = arctan(b/a)$

])

= Change of Basis

To transform a linear transformation $M_A$ in basis $A$ to basis $B$:
$
M_B = P^(-1)_(A -> B) M_A P_(B -> A)
$

Here, $P$ is calculated as:
- Express each $b_i$ (basis $B$) in terms of basis $A$: $[b_i]_A = x_i$, where $A x_i = b_i$.
- Construct $P = mat([b_1]_A, ..., [b_n]_A)$.

*Intuition:*  
- $e_1$ in basis $B$ equals $b_1$, written as $[b_1]_A = x_1$ such that $A x_1 = b_1$.
- Transform in basis $A$, then "undo" the change of basis.

*Example:*  
Given $A = mat(e_1, e_2, e_3)$ and $B = mat(b_1, b_2, b_3)$:  
1. Compute $[b_1]_A, [b_2]_A, [b_3]_A$ to find $P$.  
2. Use $M_B = P^(-1) M_A P$.

= Eigenvalues and Eigenvectors

Basically we want to find the Eigenvalues $lambda$ s.t. $A x = lambda x => (A - lambda I) x = 0 => det(A-lambda I) = 0$, where the $x$ which satisfy this for their given $lambda$ are called Eigenvectors.

Since $A v_i = lambda_i v_i = v_i lambda_i => A V = V Lambda => A = V Lambda V^(-1) => A^k = V Lambda^k V^(-1)$.


== Terms

- The set of Eigenvectors is called the *spectrum*.
- The *characteristic polynomial* is $det(A - lambda I) = 0$
- The set of vectors corresponding to a $lambda$ s.t. $A v = lambda v$ are called an *Eigenspace*.
- *Multiplicities:*
  - The number of times an eigenvalue appears as a root of the characteristic polynomial is called *algebraic multiplicity*.
  - The *geometric multiplicity* of $lambda$ is the dimension of the Eigenspace of $lambda$. Calculate as $dim(N(A - lambda I))$
  - Key rule: $"Geometric multiplicity" <= "Algebraic multiplicity"$

== Observations

- If $lambda$ is real, then it has a corresponding real Eigenvectors
- If for a real matrix $(lambda, v)$ is a complex EVal/EVec pair, then $(overline(lambda), overline(v))$ is too.
- For orthonormal matrices $lambda in CC and abs(lambda) = 1$.
- $A^k v = lambda^k v$
- $det(A - lambda I)$ is a polynomial in $lambda$ with degree $n$.
  - The coefficient of $lambda^n$ is $(-1)^n$.
- For $k$ distinct Eigenvalues, there exist $k$ independent Eigenvectors.
- The characteristic polynomial can be factored as $0 = det(A-x I) = (-1)^n (x - lambda_1)dot ... dot (x-lambda_n)$.
- $det(A) = product lambda_i$ because $det(A) = det(A - 0 I) = (-1)^n dot (lambda_1) dot ... dot (-lambda_n)$
- $"Tr"(A) = sum lambda_i$. (Also $"Tr"(A B) = "Tr"(B A) and "Tr"(A (B C)) = "Tr"((B C) A)$)
- A projection matrix $P$ projecting onto $U in RR^n$ has two Eigenvalues of $0, 1$.

*Gotchas:*
- Even though the Eigenvalues of $A, A^T$ are same, their Eigenvectors differ.
- The Eigenvalues of $A + B$ cannot be trivially determined.
- The Eigenvalues of $A B$ or $B A$ are not trivially determined. (Unless $A,B$ have equal dimensional square matrices, then they share the non-zero Eigenvalues, but might have different multiplicities.)
- Gauss Elimination doesn't preserve Eigenvalues and Eigenvectors.

== Dynamic Systems

Write down equation in the form of $arrow(g)_n = M arrow(g)_(n-1)$ with $g_0$ being the base case. Let $g in RR^m$. Since $g_n = M^n g_0$ we have that $M in RR^(m times m)$, hence quadratic. Let $v_1,...,v_m$ be the Eigenvectors of $M$.

1. *Check dimensions:*  If $"span"{v_1,...,v_m} != RR^m$ quit.
2. *Eigenbasis:* Let $V = mat(v_1, ..., v_m)$ form the new basis of $RR^m$.
3. *Exponentiation:* We have $g_n = M^n g_0 = V Lambda^n V^(-1) g_0$. Extract your solution from $g_n$.

= Similar Matrices and Spectral Theorem

$A, B$ are called similar matrices if $exists S "s.t." B = S^(-1) A S$. Similar matrices are equal dimensional square matrices. Similar matrices share Eigenvalues.

- *Spectral Theorem:* Any symmetric matrix has $n$ Eigenvalues and an orthonormal basis made out of Eigenvectors of $A$.
- Symmetric matrices can be diagonalized as $S = V Lambda V^(-1) = V Lambda V^T$. 
- The rank of a symmetric matrix is the number of non-zero Eigenvalues.
- $S = sum_(i = 1)^n lambda_i v_i v_i^T$.
- Symmetric matrices only have real Eigenvalues.

== Rayleigh Quotient

$A v = lambda v => v^T A v = lambda v^T v => lambda = R(v) = (v^T A v)/(v^T v)$.

$lambda_min <= R(v) <= lambda_max$

= Definiteness

- *Positive Semidefinite (PSD):* $lambda_i >= 0$
- *Positive Definite (PD):* $lambda_i > 0$

*Intuition:* Look at the quadratic form $q(x) = x^T A x$. If it always makes a positive ellipsoid it's PD and it's postive Eigenvalues show that growth. If it touches 0 (except for origin) it's PSD.

- If $A, B$ are PSD/PD then $A+B$ is also PSD/PD, because $x^T A x + x^T B x >= 0 => x^T (A + B) x$

= Gram Matrices

$G = V^T V$, $G$ is called a Gram matrix.

*Properties:*
- $A^T A in RR^(n times n)$ and $A A^T in RR^(m times m)$ have the same non-zero Eigenvalues.

= SVD

Any matrix $A$ can be factored as $A = U Sigma V^T$.

- $U$ has the *left-singular vectors* and is orthonormal.
- $V$ has the *right-singular vectors* and is orthonormal.
- $Sigma$ has the *singular values* and contains non-negative values only.

*Construction:*

- $A^T A = U Lambda_1 U^T$. Here we have that $Lambda_1 = Sigma^T Sigma$. $Sigma = "diag"(sigma_1, ..., sigma_k) "s.t." k = min(n,m)$
- $A A^T = V Lambda_2 V^T$. Here we have that $Lambda_2 = Sigma Sigma^T$. $Sigma = "diag"(sigma_1, ..., sigma_k) "s.t." k = min(n,m)$
- $sigma_i = sqrt(lambda_i)$.
- For both: $Sigma$ is constructed s.t. $sigma_1 >= ... >= sigma_k >= 0$. Rank: number of non-zero singular values.
